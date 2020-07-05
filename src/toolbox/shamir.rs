use curve25519_dalek::scalar::Scalar;
use rand::{CryptoRng, RngCore};
use rand::prelude::ThreadRng;
use std::cmp::Ordering;
use std::cmp::max;
use std::clone::Clone;
use log::info;
use crate::toolbox::util;
use crate::toolbox::secrets::{SecretSharing, Share};

/// A struct holding useful information about a Shamir secret sharing execution.
///
/// By convention, the shares are encoded as a Vector of singular Scalars.  The x value for each share is its index in
/// the Vector, plus 1.  Thus, if shares[2] = 1990, we are really representing the point (3, 1990).  We do this because
/// in SSS, the point at x = 0 is the secret value, and we want to avoid any chance that someone will leave the secret
/// sitting in the shares object and then pass it somewhere it shouldn't go.
pub struct Shamir<R: CryptoRng + RngCore> {
    threshold: usize,
    rng: R,
}

#[derive(Debug, Clone, Copy)]
pub struct ShamirShare {
    x: Scalar,              // the x value of the share
    y: Option<Scalar>,      // the f(x) value of the share.
}

impl Share for ShamirShare {
    fn get_value(&self) -> Scalar {
        return self.y.unwrap();
    }
}

// impl Ord for ShamirShare {
//     fn cmp(&self, other: &Self) -> Ordering {
//         return self.partial_cmp(other).unwrap();
//     }
// }

// impl PartialOrd for ShamirShare {
//     // order by x values, then by y values
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         let xorder = util::compare_scalars(&self.x, &other.x);
//         if xorder == Ordering::Equal {
//             return match (self.y, other.y) {
//                 (None,    None)    => Some(Ordering::Equal),
//                 (None,    Some(_)) => Some(Ordering::Less),
//                 (Some(_), None)    => Some(Ordering::Greater),
//                 (Some(a), Some(b)) => Some(util::compare_scalars(&a, &b)),
//             };
//         } else {
//             return Some(xorder);
//         }
//     }
// }

// impl PartialEq for ShamirShare {
//     fn eq(&self, other: &Self) -> bool {
//         return self.x == other.x && self.y == other.y;
//     }
// }

// impl Eq for ShamirShare {}

/// Given a set of polynomial coefficients, calculate the value of the polynomial at x.
fn calc_polynomial(coefficients: &Vec<Scalar>, x: &Scalar) -> Scalar {
    let mut ret = Scalar::zero();

    for (i, coefficient) in coefficients.iter().enumerate() {
        let xp = util::pow(&x, i);
        ret += xp * coefficient;
    };
    ret
}

/// Perform a Lagrange evaluation assuming the xis are true input x's, NOT off-by-one like SecretShare::shares.
fn evaluate_lagrange(x: Scalar, xis: &Vec<Scalar>, yis: &Vec<Scalar>) -> Result<Scalar, String> {
    if xis.len() != yis.len() {
        return Err(String::from("Lengths of xis and yis are not equal; you've passed invalid points"));
    }

    let mut sum = Scalar::zero();

    for (x_i, y_i) in xis.iter().zip(yis.iter()) {
        let mut term_i = y_i.clone();
        for x_j in xis.iter() {
            if x_i == x_j { continue };

            // multiply by the numerator first
            let numerator = x - x_j;
            term_i *= numerator;

            // then divide by the denominator (multiply by the inverse, since Scalar doesn't support .Div)
            let denominator = (x_i - x_j).invert();
            term_i *= denominator;
        };

        sum += term_i;
    };
    Ok(sum)
}

impl<R> Shamir<R> where R: RngCore + CryptoRng {
    pub fn new(threshold: usize, rng: R) -> Self {
        Shamir {
            threshold,
            rng
        }
    }
}

impl Shamir<ThreadRng> {
    pub fn new_without_rng(threshold: usize) -> Self {
        Shamir { threshold , rng: rand::thread_rng() }
    }
}

impl<R> SecretSharing for Shamir<R> where R: RngCore + CryptoRng {

    fn share(&mut self, secret: &Scalar, nr_of_shares: usize) -> Result<Vec<Box<dyn Share>>, String> {

        // first, select random coefficients for each term (less the first) in the polynomial
        let mut coefficients: Vec<Scalar> = Vec::new();
        let my_secret = secret.clone();
        coefficients.push(my_secret);  // the coefficient for x^0 is the secret
        for _ in 1..(self.threshold) {
            coefficients.push(Scalar::random(&mut self.rng));
        }

        // now, calculate points on the line as our shares.
        // we encode the x value as the index of the vec
        let mut shares = Vec::new();
        for i in 0..nr_of_shares {
            let x = Scalar::from((i+1) as u64);
            let y = calc_polynomial(&coefficients, &x);
            shares.push(ShamirShare { x, y: Some(y) });
        }

        return Ok(shares.iter().map(|s| Box::from(*s) as Box<dyn Share>).collect());
    }

    /// GNote that the new shares have NO GUARANTEE of being derived from the same polynomial as the provided ones.  
    /// We pick an all-new polynomial which fits the provided points.
    ///
    /// The sparse_shares vector should follow the "index + 1 = x" convention, but is allowed to contain None values
    /// to represent missing shares.  DO NOT include the secret in sparse_shares, as it is passed in separately.
    fn complete(&mut self, secret: &Scalar, sparse_shares: &Vec<Option<Box<dyn Share>>>) -> Result<Vec<Box<dyn Share>>, String> {
        if self.threshold == 0 {
            // Threshold of 0 should be impossible, since it's going to at least have a single point (the secret)
            return Err(String::from("Threshold of zero is invalid for Shamir's Secret Sharing"));
        }
        // } else if self.threshold == 1 {
        //     // If threshold is 1, we're reconstructing a single point.  The polynomial is y = secret.
        //     return Ok(sparse_shares.iter().map(|s| match s { Some(x) => Some(*x), None => Some(*secret)}).collect())
        // }

        // Set up our data structures for later reference.  Initially, `empties` will contain all of the shares with
        // y = None, and `points` has all the points with Some.  As we go, we'll build up `points` even more by taking
        // from `empties`.
        let mut empties: Vec<ShamirShare> = Vec::new();
        let mut points: Vec<ShamirShare> = Vec::new();
        points.push(ShamirShare { x: Scalar::zero(), y: Some(*secret) } );

        for (xi, share) in sparse_shares.iter().enumerate() {
            if share.is_some() {
                points.push(share.unwrap() as ShamirShare);
            } else {
                empties.push(ShamirShare { x: Scalar::from((xi + 1) as u64), y: None });
            }
        }

        info!("Asked to complete w/ threshold {} and {} shares", self.threshold, points.len() - 1);

        // STEP ONE: if the total number of points we have (sparse_shares + secret) is < threshold, we need to generate
        // random points to fill in the gaps.
        let nr_of_shares = points.len() - 1;
        if (nr_of_shares+1) < self.threshold {
            let remaining = self.threshold - nr_of_shares;
            for _ in 0..remaining {
                if let Some(mut share) = empties.pop() {
                    let yi = Scalar::random(&mut self.rng);
                    share.y = Some(yi);
                    points.push(share);
                }
            }
        }

        let (xis, yis): (Vec<Scalar>, Vec<Scalar>) = points.iter().map(|share| (share.x, share.y.unwrap())).unzip();
        let xis: Vec<Scalar> = xis[0..self.threshold].to_vec();
        let yis: Vec<Scalar> = yis[0..self.threshold].to_vec();

        // STEP TWO: if we were given more than enough points, verify the extras are on the line.  In this case, none
        // of the points have been randomly generated by us.
        if (nr_of_shares+1) > self.threshold {
            for point in points[self.threshold..].to_vec() {
                let yi = evaluate_lagrange(point.x, &xis, &yis);
                if yi.unwrap() != point.y.unwrap() {
                    return Err(format!("Extraneous point {:?} is not on the line!", point));
                }
            }
        }

        // STEP THREE: if we have any remaining empty spots, we can Lagrange-calculate their values
        for mut share in empties.into_iter() {
            match evaluate_lagrange(share.x, &xis, &yis) {
                Ok(yi) => {
                    share.y = Some(yi);
                    points.push(share);
                },
                Err(e) => return Err(e),
            }
        }

        return Ok(points[1..].to_vec());
    }

    /// Given enough shares, output the secret.
    fn reconstruct(&mut self, shares: &Vec<ShamirShare>) -> Result<Scalar, String> {
        let mut xis: Vec<Scalar> = Vec::new();
        let mut yis: Vec<Scalar> = Vec::new();
        for s in shares.iter() {
            xis.push(s.x);
            yis.push(s.y.unwrap());
        }

        info!("Reconstructing from {} shares w/ threshold {}", shares.len(), self.threshold);

        if self.threshold > shares.len() {
            return Err(String::from("Not enough shares to meet the threshold"));
        }

        let actual_threshold = max(1, self.threshold);
        let secret = evaluate_lagrange(Scalar::zero(), &xis[0..actual_threshold].to_vec(), &yis[0..actual_threshold].to_vec());
        // we use the remaining shares to do validation, and make sure ALL the points line up
        for i in actual_threshold..xis.len() {
            let y_i = yis[i];

            let y_maybe = evaluate_lagrange(xis[i], &xis[0..actual_threshold].to_vec(), &yis[0..actual_threshold].to_vec());
            if let false = y_i == y_maybe.unwrap() {
                return Err(String::from("Not all values fit into reconstruction"));
            };
        };

        return secret;
    }
}

#[allow(unused_imports)]
mod tests {
    use super::*;
    use crate::toolbox::secrets::SecretSharing;

    const one: Scalar = Scalar::one();

    // The tests in this module are generally written around the polynomial y = 
    const first:  ShamirShare = ShamirShare { x: Scalar::from(1u32), y: Some(Scalar::from(272u32))};
    const second: ShamirShare = ShamirShare { x: Scalar::from(2u32), y: Some(Scalar::from(935u32))};
    const third:  ShamirShare = ShamirShare { x: Scalar::from(3u32), y: Some(Scalar::from(1990u32))};
    const fourth: ShamirShare = ShamirShare { x: Scalar::from(4u32), y: Some(Scalar::from(3437u32))};

    #[test]
    fn shamir_polynomial_easy() {
        let coefficients = vec![one, one, one];
        assert_eq!(Scalar::from(3u32), calc_polynomial(&coefficients, &one));
        assert_eq!(Scalar::from(111u32), calc_polynomial(&coefficients, &Scalar::from(10u32)));
    }

    #[test]
    fn shamir_polynomial_medium() {
        let coefficients = vec![Scalar::from(1234u32), Scalar::from(2345u32), Scalar::from(3456u32)];
        assert_eq!(Scalar::from(7035u32), calc_polynomial(&coefficients, &one));
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
        let shares = vec![first, second, third];
        let mut sham = Shamir::new_without_rng(4);
        match sham.reconstruct(&shares) {
            Ok(_) => assert!(false, "Should not have been able to reconstruct!"),
            Err(e) => assert!(e.contains("Not enough shares")),
        };
    }

    #[test]
    fn shamir_reconstruct_easy() {
        let shares = vec![first, second, third];
        let mut sham = Shamir::new_without_rng(shares.len());
        match sham.reconstruct(&shares) {
            Ok(r1) => assert_eq!(one, r1),
            Err(e) => assert!(false, format!("Error reconstructing: {}", e)),
        }
    }

    #[test]
    fn shamir_reconstruct_easy_with_leftovers() {
        let shares = vec![first, second, third, fourth];
        let mut sham = Shamir::new_without_rng(3);
        match sham.reconstruct(&shares) {
            Ok(r1) => assert_eq!(one, r1),
            Err(e) => assert!(false, format!("Error reconstructing: {}", e)),
        }
    }

    #[test]
    fn shamir_reconstruct_medium() {
        let mut rng = rand::thread_rng();
        let secret = Scalar::random(&mut rng);
        let mut sham = Shamir::new_without_rng(10);
        let shares = sham.share(&secret, 20);
        assert!(shares.is_ok());
        match sham.reconstruct(&shares.unwrap()[0..10].to_vec()) {
            Err(e) => assert!(false, "Error reconstructing: {}", e),
            Ok(val) => assert_eq!(secret, val),
        }
    }

    #[test]
    fn shamir_reconstruct_medium_with_leftovers() {
        let mut rng = rand::thread_rng();
        let secret = Scalar::random(&mut rng);
        let mut sham = Shamir::new_without_rng(10);
        let shares = sham.share(&secret, 20);
        assert!(shares.is_ok());
        let shares = shares.unwrap();
        assert_eq!(20, shares.len());
        match sham.reconstruct(&shares) {
            Err(e) => assert!(false, "Error reconstructing: {}", e),
            Ok(val) => assert_eq!(secret, val),
        }
    }

    #[test]
    fn shamir_reconstruct_bad_leftovers() {
        // the fourth point should be 3437 for proper reconstruction; altering it should cause failure
        let shares = vec![first, second, third, ShamirShare { x: Scalar::from(4u32), y: Some(Scalar::from(3436u32))}];
        let mut sham = Shamir::new_without_rng(3);
        match sham.reconstruct(&shares) {
            Err(e) => assert!(e.contains("Not all values fit into reconstruction")),
            Ok(_) => assert!(false, "Should not have been able to reconstruct!"),
        }
    }

    #[test]
    fn shamir_reconstruct_bad_in_threshold() {
        let mut rng = rand::thread_rng();
        let secret = Scalar::random(&mut rng);

        let mut sham = Shamir::new_without_rng(10);
        let shares = sham.share(&secret, 20);
        assert!(shares.is_ok());

        let mut shares = shares.unwrap();
        shares[5] = match shares[5].y.unwrap() {
            one => ShamirShare {x: Scalar::from(6u32), y: Some(Scalar::zero())},
            _ => ShamirShare {x: Scalar::from(6u32), y: Some(Scalar::one())}
        };

        match sham.reconstruct(&shares) {
            Err(e) => assert!(e.contains("Not all values fit into reconstruction")),
            Ok(_) => assert!(false, "Should not have been able to reconstruct!"),
        };
    }

    #[test]
    fn shamir_eval_lagrange_easy() {
        let xis = vec![Scalar::from(1u32), Scalar::from(2u32), Scalar::from(3u32)];
        let yis = vec![Scalar::from(272u32), Scalar::from(935u32), Scalar::from(1990u32)];
        assert_eq!(Scalar::one(), evaluate_lagrange(Scalar::zero(), &xis, &yis).unwrap());
        assert_eq!(Scalar::from(7507u32), evaluate_lagrange(Scalar::from(6u32), &xis, &yis).unwrap());
    }

    #[test]
    fn shamir_eval_lagrange_hole() {
        let xis = vec![Scalar::from(0u32), Scalar::from(1u32), Scalar::from(3u32)];
        let yis = vec![Scalar::one(), Scalar::from(272u32), Scalar::from(1990u32)];
        assert_eq!(Scalar::from(935u32), evaluate_lagrange(Scalar::from(2u32), &xis, &yis).unwrap());
        assert_eq!(Scalar::from(7507u32), evaluate_lagrange(Scalar::from(6u32), &xis, &yis).unwrap());
    }

    #[test]
    fn shamir_complete_easy() {
        // the missing element is 935
        let yis = vec![Some(first), None, Some(third)];

        let mut sham = Shamir::new_without_rng(3);
        match sham.complete(&one, &yis) {
            Ok(shares) => {
                match sham.reconstruct(&shares) {
                    Ok(maybe_secret) => assert_eq!(one, maybe_secret),
                    Err(e) => assert!(false, "Completed the shares but couldn't reconstruct: {}", e),
                }
            },
            Err(e) => assert!(false, "Couldn't complete shares: {}", e),
        }
    }

    #[test]
    fn shamir_complete_one() {
        let yis = vec![
            Some(ShamirShare { x: one,                y: Some(one) }),
            Some(ShamirShare { x: Scalar::from(2u32), y: Some(one) }),
            Some(ShamirShare { x: Scalar::from(3u32), y: Some(one) }),
            Some(ShamirShare { x: Scalar::from(4u32), y: Some(one) }),
        ];
        let mut sham = Shamir::new_without_rng(1);
        match sham.complete(&one, &yis) {
            Ok(shares) => {
                for share in shares.iter() {
                    assert_eq!(one, share.y.unwrap());
                }
            },
            Err(e) => assert!(false, "Couldn't complete shares: {}", e),
        }
    }

    #[test]
    fn shamir_complete_one_bad() {
        let yis = vec![
            Some(ShamirShare { x: one,                y: Some(one) }),
            Some(ShamirShare { x: Scalar::from(2u32), y: Some(one) }),
            Some(ShamirShare { x: Scalar::from(3u32), y: Some(one) }),
            Some(ShamirShare { x: Scalar::from(4u32), y: Some(Scalar::from(2u32)) }),
        ];
        let mut sham = Shamir::new_without_rng(1);
        match sham.complete(&one, &yis) {
            Ok(_) => assert!(false, "Should not have been able to complete"),
            Err(e) => assert!(e.contains("is not on the line")),
        }
    }
}
