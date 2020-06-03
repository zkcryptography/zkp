use curve25519_dalek::scalar::Scalar;
use rand::{CryptoRng, RngCore};
use std::cmp::Ordering;

// A struct holding useful information about a Shamir secret sharing execution.
//
// By convention, the shares are encoded as a Vector of singular Scalars.  The x value for each share is its index in
// the Vector, plus 1.  Thus, if shares[2] = 1990, we are really representing the point (3, 1990).  We do this because
// in SSS, the point at x = 0 is the secret value, and we want to avoid any chance that someone will leave the secret
// sitting in the shares object and then pass it somewhere it shouldn't go.
#[derive(Clone)]
pub struct SecretShare {
    secret: Scalar,
    pub shares: Vec<Scalar>,
    threshold: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct Share {
    x: Scalar,
    y: Option<Scalar>,
}

impl Ord for Share {
    fn cmp(&self, other: &Self) -> Ordering {
        return self.partial_cmp(other).unwrap();
    }
}

impl PartialOrd for Share {
    // order by x values, then by y values
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let xorder = compare_scalars(&self.x, &other.x); 
        if xorder == Ordering::Equal {
            return match (self.y, other.y) {
                (None,    None)    => Some(Ordering::Equal),
                (None,    Some(_)) => Some(Ordering::Less),
                (Some(_), None)    => Some(Ordering::Greater),
                (Some(a), Some(b)) => Some(compare_scalars(&a, &b)),
            };
        } else {
            return Some(xorder);
        }
    }
}

impl PartialEq for Share {
    fn eq(&self, other: &Self) -> bool {
        return self.x == other.x && self.y == other.y;
    }
}

impl Eq for Share {}

// Compare two Scalar values.
fn compare_scalars(a: &Scalar, b: &Scalar) -> Ordering {
    let abytes = a.to_bytes();
    let bbytes = b.to_bytes();
    for i in 0..32 {
        let o: Ordering = abytes[i].cmp(&bbytes[i]);
        if o != Ordering::Equal {
            return o;
        }
    }
    return Ordering::Equal;
}

// Given a set of polynomial coefficients, calculate the value of the polynomial at x.
fn calc_polynomial(coefficients: &Vec<Scalar>, x: &Scalar) -> Scalar {
    let mut ret = Scalar::zero();

    for i in 0..coefficients.len() {
        let xp = pow(&x, i);
        ret += xp * coefficients[i];
    };
    ret
}

// Raise a Scalar to an arbitrary power.  This code is SUPER dumb: not efficient and not constant-time.
fn pow(x: &Scalar, p: usize) -> Scalar {
    if p == 0 {
        return Scalar::one();
    }

    let mut res = x.clone();
    for _ in 1..p {
        res *= x;
    }
    res
}

// Perform a Lagrange evaluation assuming the xis are true input x's, NOT off-by-one like SecretShare::shares.
fn evaluate_lagrange(x: Scalar, xis: &Vec<Scalar>, yis: &Vec<Scalar>) -> Scalar {
    let mut sum = Scalar::zero();

    for (x_i, y_i) in xis.iter().zip(yis.iter()) {
        let mut term_i = y_i.clone();
        for x_j in xis.iter() {
            if x_i == x_j { continue };

            // multiply by the numerator first
            let numerator = x - x_j;
            term_i *= numerator;

            // then multiply by the inverse of the denominator
            let denominator = (x_i - x_j).invert();
            term_i *= denominator;
        };

        sum += term_i;
    };
    sum
}

impl SecretShare {

    // Given a secret and some other information, calculate a set of shares using Shamir's Secret Sharing.  We don't
    // expect this code to ever be called by our application, but it's useful for testing.
    pub fn share<R: RngCore + CryptoRng>(secret: &Scalar, nr_of_shares: usize, threshold: usize, rng: &mut R) -> SecretShare {

        // first, select random coefficients for each term (less the first) in the polynomial
        let mut coefficients: Vec<Scalar> = Vec::new();
        let my_secret = secret.clone();
        coefficients.push(my_secret);  // the coefficient for x^0 is the secret
        for _ in 1..(threshold) {
            coefficients.push(Scalar::random(rng));
        }

        // now, calculate points on the line as our shares.
        // we encode the x value as the index of the vec
        let mut shares: Vec<Scalar> = Vec::new();
        for i in 0..nr_of_shares {
            let x = Scalar::from((i+1) as u64);
            let y = calc_polynomial(&coefficients, &x);
            shares.push(y);
        }

        SecretShare {secret: my_secret, shares, threshold}
    }

    // Given some shares and the secret, compute a valid set of additional shares.  Note that the new shares have
    // NO GUARANTEE of being derived from the same polynomial as the provided ones.  We pick an all-new polynomial
    // which fits the provided points.  Camenish refers to this function as cmpl_Gamma in his thesis.
    // 
    // The sparse_shares vector should follow the "index + 1 = x" convention, but is allowed to contain Option values
    // to represent missing shares.  DO NOT include the secret in sparse_shares, as it is passed in separately.
    pub fn complete<R: CryptoRng + RngCore>(secret: Scalar, threshold: usize, sparse_shares: &Vec<Option<Scalar>>, rng: &mut R) -> Result<SecretShare, String> {
        let mut nr_of_shares = 0;
        let mut points: Vec<Share> = Vec::new();
        for (xi, share) in sparse_shares.iter().enumerate() {
            let x = Scalar::from((xi + 1) as u64);
            let mut s = Share {x, y: None};
            if share.is_some() {
                nr_of_shares += 1;
                s.y = share.clone()
            };
            points.push(s);
        }
        points.insert(0, Share { x: Scalar::zero(), y: Some(secret) } );

        // at this point, `empties` contains all of the points with None, and `points` has all the points with Some
        // we'll build `points` up even more by taking from `empties`
        let mut empties: Vec<Share> = points.iter().filter(|s| s.y.is_none()).cloned().collect();
        let mut points: Vec<Share> = points.iter().filter(|s| s.y.is_some()).cloned().collect();

        // STEP ONE: if the total number of points we have (sparse_shares + secret) is < threshold, we need to generate
        // random points to fill in the gaps.
        if (nr_of_shares+1) < threshold {
            let remaining = threshold - nr_of_shares;
            for _ in 0..remaining {
                if let Some(mut share) = empties.pop() {
                    let yi = Scalar::random(rng);    // TODO I believe in normal usage this should be the PRNG from the transcript, so we always generate the same "random" challenges?
                    share.y = Some(yi);
                    points.push(share);
                }
            }
        }

        let (xis, yis): (Vec<Scalar>, Vec<Scalar>) = points.iter().map(|share| (share.x, share.y.unwrap())).unzip();
        let xis: Vec<Scalar> = xis[0..threshold].to_vec();
        let yis: Vec<Scalar> = yis[0..threshold].to_vec();

        // STEP TWO: if we were given more than enough points, verify the extras are on the line.  In this case, none
        // of the points have been randomly generated by us.
        if (nr_of_shares+1) >= threshold {
            for point in points[threshold..].to_vec() {
                let yi = evaluate_lagrange(point.x, &xis, &yis);
                if yi != point.y.unwrap() {
                    return Err(format!("Extraneous point {:?} is not on the line!", point));
                }
            }
        }

        // STEP THREE: if we have any remaining empty spots, we can Lagrange-calculate their values
        for mut share in empties.pop() {
            let yi = evaluate_lagrange(share.x, &xis, &yis);
            share.y = Some(yi);
            points.push(share);
        }

        let mut new_shares = points[1..].to_vec();
        new_shares.sort();
        let new_shares = new_shares.iter().map(|n| n.y.unwrap()).collect();
        Ok(SecretShare {
            secret,
            shares: new_shares,
            threshold: threshold,
        })
    }

    // Given enough shares, output the secret
    pub fn reconstruct(threshold: usize, shares: Vec<Scalar>) -> Result<Scalar, String> {
        if threshold > shares.len() {
            return Err(String::from("Not enough shares to meet the threshold"));
        }

        // From Handbook of Applied Cryptography, 12.71:
        //     S = sum(i=1..t){c_i*y_i}, where c_i = TT(j=1..t, j!=i){x_j / (x_j - x_i)}
        let mut sum: Scalar = Scalar::zero();

        // we use the first set of shares to reconstruct the secret
        for i in 0..threshold {
            let y_i = shares[i];

            let mut c_i = 1f64;

            for j in 0..threshold {
                if i == j { continue; }
                c_i *= ((j+1) as f64) / ((j+1) as f64 - (i+1) as f64);
            }

            // The From trait on Scalar only supports unsigned numerical types, so we have to kinda hack this
            let c_i = match c_i < 0.0 {
                true => -Scalar::from((-c_i) as u64),
                false => Scalar::from(c_i as u64),
            };

            let delta = c_i * y_i;
            sum += delta;
        }

        let mut xis: Vec<Scalar> = Vec::new();
        for i in 1..(threshold+1) {
            xis.push(Scalar::from(i as u64));
        }
        let yis = shares[0..threshold].to_vec();

        // we use the remaining shares to do validation, and make sure ALL the points line up
        for i in threshold..shares.len() {
            let y_i = shares[i];

            let y_maybe = evaluate_lagrange(Scalar::from((i+1) as u64), &xis, &yis);
            if let false = y_i == y_maybe {
                return Err(String::from("Not all values fit into reconstruction"));
            };
        };

        return Ok(sum);
    }
}

mod tests {
    use super::*;

    #[test]
    fn shamir_pow_easy() {
        for p in vec![0, 1, 2, 4] {
            let val = pow(&Scalar::one(), p);
            assert_eq!(Scalar::one(), val);
        };
    }

    #[test]
    fn shamir_pow_medium() {
        let val = pow(&Scalar::from(2u32), 2);
        assert_eq!(Scalar::from(4u32), val);

        let val = pow(&Scalar::from(8u32), 2);
        assert_eq!(Scalar::from(64u32), val);

        let val = pow(&Scalar::from(9u32), 3);
        assert_eq!(Scalar::from(729u32), val);
    }

    #[test]
    fn shamir_pow_overflow() {
        // in decimal, 5383850369160867882082008644310060803097890751578601301633528521931415479118
        let the_scalar = Scalar::from_canonical_bytes([78, 227, 105, 171, 173, 162, 96, 141, 241, 244, 32, 246, 255, 9, 210, 32, 110, 245, 179, 133, 8, 34, 83, 32, 220, 162, 102, 9, 189, 38, 231, 11]).unwrap();

        // in decimal, 905024118957487278709981156877405425812244224552873609041215153919592868854
        let the_answer = Scalar::from_canonical_bytes([246, 171, 1, 72, 68, 73, 121, 162, 178, 134, 163, 34, 136, 171, 117, 234, 5, 196, 64, 75, 61, 139, 40, 49, 68, 126, 27, 73, 186, 57, 0, 2]).unwrap();
        let val = pow(&the_scalar, 32);
        assert_eq!(the_answer, val);
    }

    #[test]
    fn shamir_polynomial_easy() {
        let coefficients = vec![Scalar::one(), Scalar::one(), Scalar::one()];
        assert_eq!(Scalar::from(3u32), calc_polynomial(&coefficients, &Scalar::one()));
        assert_eq!(Scalar::from(111u32), calc_polynomial(&coefficients, &Scalar::from(10u32)));
    }

    #[test]
    fn shamir_polynomial_medium() {
        let coefficients = vec![Scalar::from(1234u32), Scalar::from(2345u32), Scalar::from(3456u32)];
        assert_eq!(Scalar::from(7035u32), calc_polynomial(&coefficients, &Scalar::one()));
        assert_eq!(Scalar::from(19748u32), calc_polynomial(&coefficients, &Scalar::from(2u32)));
        assert_eq!(Scalar::from(3458346234u32), calc_polynomial(&coefficients, &Scalar::from(1000u32)));
    }

    #[test]
    fn shamir_polynomial_overflow() {
        let coefficients = vec![Scalar::from(1234u32), Scalar::from(2345u32), Scalar::from(3456u32)];

        // in decimal, 5383850369160867882082008644310060803097890751578601301633528521931415479118
        let the_scalar = Scalar::from_canonical_bytes([78, 227, 105, 171, 173, 162, 96, 141, 241, 244, 32, 246, 255, 9, 210, 32, 110, 245, 179, 133, 8, 34, 83, 32, 220, 162, 102, 9, 189, 38, 231, 11]).unwrap();

        let the_answer = Scalar::from_canonical_bytes([207, 201, 245, 205, 49, 252, 35, 17, 31, 231, 204, 52, 247, 29, 32, 244, 189, 253, 92, 38, 214, 28, 252, 104, 227, 175, 60, 192, 164, 153, 169, 8]).unwrap();
        assert_eq!(the_answer, calc_polynomial(&coefficients, &the_scalar));
    }

    #[test]
    fn shamir_reconstruct_bad_threshold() {
        let shares = vec![Scalar::from(272u32), Scalar::from(935u32), Scalar::from(1990u32)];
        match SecretShare::reconstruct(4, shares) {
            Ok(_) => assert!(false, "Should not have been able to reconstruct!"),
            Err(e) => assert!(e.contains("Not enough shares")),
        };
    }

    #[test]
    fn shamir_reconstruct_easy() {
        let secret = Scalar::one();
        let shares = vec![Scalar::from(272u32), Scalar::from(935u32), Scalar::from(1990u32)];
        let r1 = SecretShare::reconstruct(shares.len(), shares).unwrap();
        assert_eq!(secret, r1);
    }

    #[test]
    fn shamir_reconstruct_easy_with_leftovers() {
        let secret = Scalar::one();
        let shares = vec![Scalar::from(272u32), Scalar::from(935u32), Scalar::from(1990u32), Scalar::from(3437u32)];
        let r1 = SecretShare::reconstruct(3, shares).unwrap();
        assert_eq!(secret, r1);
    }

    #[test]
    fn shamir_reconstruct_medium() {
        let mut rng = rand::thread_rng();
        let secret = Scalar::random(&mut rng);
        let obj = SecretShare::share(&secret, 20, 10, &mut rng);
        match SecretShare::reconstruct(10, obj.shares[0..10].to_vec()) {
            Err(e) => assert!(false, "Error reconstructing: {}", e),
            Ok(val) => assert_eq!(secret, val),
        }
    }

    #[test]
    fn shamir_reconstruct_medium_with_leftovers() {
        let mut rng = rand::thread_rng();
        let secret = Scalar::random(&mut rng);
        let obj = SecretShare::share(&secret, 20, 10, &mut rng);
        assert_eq!(20, obj.shares.len());
        match SecretShare::reconstruct(10, obj.shares) {
            Err(e) => assert!(false, "Error reconstructing: {}", e),
            Ok(val) => assert_eq!(secret, val),
        }
    }

    #[test]
    fn shamir_reconstruct_bad_leftovers() {
        // the fourth point should be 3437 for proper reconstruction; altering it should cause failure
        let shares = vec![Scalar::from(272u32), Scalar::from(935u32), Scalar::from(1990u32), Scalar::from(3436u32)];
        match SecretShare::reconstruct(3, shares) {
            Err(e) => assert!(e.contains("Not all values fit into reconstruction")),
            Ok(_) => assert!(false, "Should not have been able to reconstruct!"),
        }
    }

    #[test]
    fn shamir_reconstruct_bad_in_threshold() {
        let mut rng = rand::thread_rng();
        let secret = Scalar::random(&mut rng);
        let mut obj = SecretShare::share(&secret, 20, 10, &mut rng);
        obj.shares[5] = if obj.shares[5] == Scalar::one() { Scalar::zero() } else { Scalar::one() };
        match SecretShare::reconstruct(10, obj.shares) {
            Err(e) => assert!(e.contains("Not all values fit into reconstruction")),
            Ok(_) => assert!(false, "Should not have been able to reconstruct!"),
        };
    }

    #[test]
    fn shamir_eval_lagrange_easy() {
        let xis = vec![Scalar::from(1u32), Scalar::from(2u32), Scalar::from(3u32)];
        let yis = vec![Scalar::from(272u32), Scalar::from(935u32), Scalar::from(1990u32)];
        assert_eq!(Scalar::one(), evaluate_lagrange(Scalar::zero(), &xis, &yis));
        assert_eq!(Scalar::from(7507u32), evaluate_lagrange(Scalar::from(6u32), &xis, &yis));
    }

    #[test]
    fn shamir_eval_lagrange_hole() {
        let xis = vec![Scalar::from(0u32), Scalar::from(1u32), Scalar::from(3u32)];
        let yis = vec![Scalar::one(), Scalar::from(272u32), Scalar::from(1990u32)];
        assert_eq!(Scalar::from(935u32), evaluate_lagrange(Scalar::from(2u32), &xis, &yis));
        assert_eq!(Scalar::from(7507u32), evaluate_lagrange(Scalar::from(6u32), &xis, &yis));
    }

    #[test]
    fn shamir_complete_easy() {
        let mut rng = rand::thread_rng();
        let secret = Scalar::one();
        // the missing element is 935
        let yis = vec![Some(Scalar::from(272u32)), None, Some(Scalar::from(1990u32))];
        match SecretShare::complete(secret, 3, &yis, &mut rng) {
            Ok(shareobj) => {
                match SecretShare::reconstruct(3, shareobj.shares) {
                    Ok(maybe_secret) => assert_eq!(secret, maybe_secret),
                    Err(e) => assert!(false, "Completed the shares but couldn't reconstruct: {}", e),
                }
            },
            Err(e) => assert!(false, "Couldn't complete shares: {}", e),
        }
    }
}
