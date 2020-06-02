use curve25519_dalek::scalar::Scalar;
use rand::{CryptoRng, RngCore};

#[derive(Clone)]
pub struct SecretShare {
    secret: Scalar,
    pub shares: Vec<Scalar>,
    threshold: usize,
}

impl SecretShare {

    // We don't expect this code to ever be called by our application, but it's useful for testing
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
            let y = SecretShare::calc_polynomial(&coefficients, &x);
            shares.push(y);
        }

        SecretShare {secret: my_secret, shares, threshold}
    }

    // Given a set of polynomial coefficients, calculate the value of the polynomial at x
    fn calc_polynomial(coefficients: &Vec<Scalar>, x: &Scalar) -> Scalar {
        let mut ret = Scalar::zero();

        for i in 0..coefficients.len() {
            let xp = SecretShare::pow(&x, i);
            ret += xp * coefficients[i];
        };
        ret
    }

    // Raise a Scalar to an arbitrary power.  This code is SUPER dumb and assumes public exponents
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

    // Given some shares and the secret, compute the rest of the shares
    // in normal usage, we have a share which is a random value, one for each of the secret values in a proof which we DO NOT know
    // Each entry in shares is either None or Some(random_value).
    //      If it's None, that means for the secret var at this index, we have a secret value we want to communicate knowledge of.
    //          Implies we should only have one None value in our `shares` Vec
    //      If it's Some, the enclosed value is a randomized challenge computed because we don't have a secret value for the given variable
    pub fn complete(secret: Scalar, shares: &mut Vec<Option<Scalar>>) -> Result<SecretShare, String> {
        let nr_of_shares = shares.iter().filter(|&n| n.is_some()).count();

        let mut output: Vec<Scalar> = shares.iter().map(|share| {
            return match share.is_some() {
                true => share.unwrap(),
                false => secret, //TODO: Shamir Secret Sharing
            };
        }).collect();
        output.insert(0, secret);
        // TODO ensure the rest of the shares are still on our curve
        Ok(SecretShare {
            secret,
            shares: output,
            threshold: nr_of_shares,
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

        // we use the remaining shares to do validation, and make sure ALL the points line up
        for i in threshold..shares.len() {
            let y_i = shares[i];
            let y_maybe = SecretShare::evaluate_lagrange((i+1) as i64, shares[0..threshold].to_vec());
            if let false = y_i == y_maybe {
                return Err(String::from("Not all values fit into reconstruction"));
            };
        };

        return Ok(sum);
    }

    fn evaluate_lagrange(x: i64, points: Vec<Scalar>) -> Scalar {
        let mut sum = Scalar::zero();
        for (i, y_i) in points.iter().enumerate() {
            let mut coeff = 1f64;
            for (j, _) in points.iter().enumerate() {
                if i == j { continue };
                let numerator = x - ((j+1) as i64);
                // println!("Numerator: {}", numerator);
                let denominator = ((i+1) as i64) - ((j+1) as i64);
                // println!("Denominator: {}", denominator);
                coeff *= (numerator as f64) / (denominator as f64);
                // println!("Val: {}", coeff);
            };
            // println!("c_{} = {}", i, coeff);
            let coeff = match coeff < 0.0 { 
                true => -Scalar::from((-coeff) as u64),
                false => Scalar::from(coeff as u64),
            };
            sum += y_i * coeff
        };
        sum
    }
}

mod tests {
    use super::*;

    #[test]
    fn shamir_pow_easy() {
        for p in vec![0, 1, 2, 4] {
            let val = SecretShare::pow(&Scalar::one(), p);
            assert_eq!(Scalar::one(), val);
        };
    }

    #[test]
    fn shamir_pow_medium() {
        let val = SecretShare::pow(&Scalar::from(2u32), 2);
        assert_eq!(Scalar::from(4u32), val);

        let val = SecretShare::pow(&Scalar::from(8u32), 2);
        assert_eq!(Scalar::from(64u32), val);

        let val = SecretShare::pow(&Scalar::from(9u32), 3);
        assert_eq!(Scalar::from(729u32), val);
    }

    #[test]
    fn shamir_pow_overflow() {
        // in decimal, 5383850369160867882082008644310060803097890751578601301633528521931415479118
        let the_scalar = Scalar::from_canonical_bytes([78, 227, 105, 171, 173, 162, 96, 141, 241, 244, 32, 246, 255, 9, 210, 32, 110, 245, 179, 133, 8, 34, 83, 32, 220, 162, 102, 9, 189, 38, 231, 11]).unwrap();

        // in decimal, 905024118957487278709981156877405425812244224552873609041215153919592868854
        let the_answer = Scalar::from_canonical_bytes([246, 171, 1, 72, 68, 73, 121, 162, 178, 134, 163, 34, 136, 171, 117, 234, 5, 196, 64, 75, 61, 139, 40, 49, 68, 126, 27, 73, 186, 57, 0, 2]).unwrap();
        let val = SecretShare::pow(&the_scalar, 32);
        assert_eq!(the_answer, val);
    }

    #[test]
    fn shamir_polynomial_easy() {
        let coefficients = vec![Scalar::one(), Scalar::one(), Scalar::one()];
        assert_eq!(Scalar::from(3u32), SecretShare::calc_polynomial(&coefficients, &Scalar::one()));
        assert_eq!(Scalar::from(111u32), SecretShare::calc_polynomial(&coefficients, &Scalar::from(10u32)));
    }

    #[test]
    fn shamir_polynomial_medium() {
        let coefficients = vec![Scalar::from(1234u32), Scalar::from(2345u32), Scalar::from(3456u32)];
        assert_eq!(Scalar::from(7035u32), SecretShare::calc_polynomial(&coefficients, &Scalar::one()));
        assert_eq!(Scalar::from(19748u32), SecretShare::calc_polynomial(&coefficients, &Scalar::from(2u32)));
        assert_eq!(Scalar::from(3458346234u32), SecretShare::calc_polynomial(&coefficients, &Scalar::from(1000u32)));
    }

    #[test]
    fn shamir_polynomial_overflow() {
        let coefficients = vec![Scalar::from(1234u32), Scalar::from(2345u32), Scalar::from(3456u32)];

        // in decimal, 5383850369160867882082008644310060803097890751578601301633528521931415479118
        let the_scalar = Scalar::from_canonical_bytes([78, 227, 105, 171, 173, 162, 96, 141, 241, 244, 32, 246, 255, 9, 210, 32, 110, 245, 179, 133, 8, 34, 83, 32, 220, 162, 102, 9, 189, 38, 231, 11]).unwrap();

        let the_answer = Scalar::from_canonical_bytes([207, 201, 245, 205, 49, 252, 35, 17, 31, 231, 204, 52, 247, 29, 32, 244, 189, 253, 92, 38, 214, 28, 252, 104, 227, 175, 60, 192, 164, 153, 169, 8]).unwrap();
        assert_eq!(the_answer, SecretShare::calc_polynomial(&coefficients, &the_scalar));
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
            Err(e) => eprint!("Error reconstructing: {}", e),
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
            Err(e) => eprint!("Error reconstructing: {}", e),
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
}
