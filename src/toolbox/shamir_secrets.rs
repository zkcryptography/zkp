use curve25519_dalek::scalar::Scalar;
use std::ops::Neg;

#[derive(Clone)]
pub struct SecretShare {
    secret: Scalar,
    pub shares: Vec<Scalar>,
    threshold: usize,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Share {
    pub x: Scalar,              // this is the x in f(x) of our polynomial
    pub y: Scalar,              // this is the f(x) of our polynomial
}

impl SecretShare {

    pub fn share(secret: &Scalar, nr_of_shares: usize, threshold: usize) -> SecretShare {
        let mut coefficients: Vec<Scalar> = Vec::new();
        let my_secret = secret.clone();
        coefficients.push(my_secret);  // the coefficient for x^0 is the secret
        for _ in 1..(threshold) {

            // TODO should this be an independent RNG, or the transcript RNG?
            // If it's the transcript's, anyone with the transcript would be able to generate the same polynomials
            //      I don't think we want that, because you could write code to do so and easily recover the secret from just a single share
            coefficients.push(Scalar::random(&mut rand::thread_rng()));
        }

        // println!("Polynomial coefficients: {:?}", coefficients);

        let mut shares: Vec<Scalar> = Vec::new();
        for i in 0..nr_of_shares {
            let x = Scalar::from((i+1) as u64);
            let y = SecretShare::calc_polynomial(&coefficients, &x);
            shares.push(y);
        }

        // println!("Generated shares: {:?}", shares);
        // select random polynomial of degree *threshold*
        // 0-coeff: secret
        // output the shares, which are points evaluated at i=1,2,3,...,nr_of_shares
        SecretShare {secret: my_secret, shares, threshold}
    }

    fn calc_polynomial(coefficients: &Vec<Scalar>, x: &Scalar) -> Scalar {
        let mut ret = Scalar::zero();

        for i in 0..coefficients.len() {
            if let Ok(xp) = SecretShare::pow(&x, i) {
                ret += xp * coefficients[i];
            }
        };
        ret
    }

    fn pow(x: &Scalar, p: usize) -> Result<Scalar, &'static str> {
        if p == 0 {
            return Ok(Scalar::one());
        } else if p == 1 {
            return Ok(x.clone());
        }

        let mut res = x.clone();
        for _ in 1..p {
            res *= x;
        }
        Ok(res)
    }


    // given some shares and the secret, compute the rest of the shares
    // in normal usage, we have a share which is a random value, one for each of the secret values in a proof which we DO NOT know

    // Each entery in shares is either None or Some(random_value).
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
        Ok(SecretShare {
            secret,
            shares: output,
            threshold: nr_of_shares,
        })
    }

    // given enough shares, output the secret
    pub fn reconstruct(shares: Vec<Scalar>) -> Result<Scalar, String> {
        // we need to know t, the threshold for shares
        // do we assume len(shares)?
        // I think this is safe, since we're the ones setting up the shares in the first place

        // From Handbook of Applied Cryptography, 12.71:
        //     S = sum(i=1..t){c_i*y_i}, where c_i = TT(j=1..t, j!=i){x_j / (x_j - x_i)}
        let mut sum: Scalar = Scalar::zero();

        for i in 0..shares.len() {
            let y_i = shares[i];
            // println!("Using point ({}, {:?})", i+1, y_i);

            let mut c_i = 1f64;

            for j in 0..shares.len() {
                if i == j { continue; }
                c_i *= ((j+1) as f64) / ((j+1) as f64 - (i+1) as f64);
            }

            // println!("c_{} = {}", i+1, c_i);

            // The From trait on Scalar only supports unsigned numerical types, so we have to kinda hack this
            // println!("c_{} as u64 = {}", i+1, (-1.0 * c_i) as u64);
            let c_i = if c_i < 0.0 { Scalar::from((-1.0 * c_i) as u64).neg() } else { Scalar::from(c_i as u64) };

            
            let delta = c_i * y_i;
            // println!("Delta is {:?}", delta);
            sum += delta;
            // println!("Sum is now {:?}", sum);
        }

        return Ok(sum);
    }

    // given enough shares, output the secret
    pub fn reconstruct_at_index(idx: usize, shares: Vec<Scalar>) -> Result<Scalar, String> {
        // From Handbook of Applied Cryptography, 12.71:
        //     S = sum(i=1..t){c_i*y_i}, where c_i = TT(j=1..t, j!=i){x_j / (x_j - x_i)}
        let mut sum: Scalar = Scalar::zero();
        for i in 0..shares.len() {
            let y_i = shares[i];

            let mut c_i = 1f64;

            for j in 0..shares.len() {
                if i == j { continue; }
                c_i *= ((j + 1 + idx) as f64) / (j as f64 - i as f64);
            }

            sum += Scalar::from(c_i as u64) * y_i;
        }

        return Ok(sum);
    }
}

mod tests {
    use super::*;

    #[test]
    fn shamir_pow_easy() {
        for p in vec![0, 1, 2, 4] {
            match SecretShare::pow(&Scalar::one(), p) {
                Err(e) => eprint!("{}", e),
                Ok(val) => assert_eq!(Scalar::one(), val),
            };
        };
    }

    #[test]
    fn shamir_pow_medium() {
        match SecretShare::pow(&Scalar::from(2u32), 2) {
            Err(e) => eprint!("{}", e),
            Ok(val) => assert_eq!(Scalar::from(4u32), val),
        };

        match SecretShare::pow(&Scalar::from(8u32), 2) {
            Err(e) => eprint!("{}", e),
            Ok(val) => assert_eq!(Scalar::from(64u32), val),
        };

        match SecretShare::pow(&Scalar::from(9u32), 3) {
            Err(e) => eprint!("{}", e),
            Ok(val) => assert_eq!(Scalar::from(729u32), val),
        };
    }

    #[test]
    fn shamir_pow_overflow() {
        // in decimal, 5383850369160867882082008644310060803097890751578601301633528521931415479118
        let the_scalar = Scalar::from_canonical_bytes([78, 227, 105, 171, 173, 162, 96, 141, 241, 244, 32, 246, 255, 9, 210, 32, 110, 245, 179, 133, 8, 34, 83, 32, 220, 162, 102, 9, 189, 38, 231, 11]).unwrap();

        // in decimal, 905024118957487278709981156877405425812244224552873609041215153919592868854
        let the_answer = Scalar::from_canonical_bytes([246, 171, 1, 72, 68, 73, 121, 162, 178, 134, 163, 34, 136, 171, 117, 234, 5, 196, 64, 75, 61, 139, 40, 49, 68, 126, 27, 73, 186, 57, 0, 2]).unwrap();
        match SecretShare::pow(&the_scalar, 32) {
            Err(e) => eprint!("{}", e),
            Ok(val) => assert_eq!(the_answer, val),
        };
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
    fn shamir_reconstruct_easy() {
        let secret = Scalar::one();
        let shares = vec![Scalar::from(272u32), Scalar::from(935u32), Scalar::from(1990u32)];

        let r1 = SecretShare::reconstruct(shares).unwrap();

        assert_eq!(secret, r1);
    }

    #[test]
    fn shamir_reconstruct_medium() {
        let mut rng = rand::thread_rng();
        let secret = Scalar::random(&mut rng);
        let obj = SecretShare::share(&secret, 20, 10);
        match SecretShare::reconstruct(obj.shares[0..10].to_vec()) {
            Err(e) => eprint!("Error reconstructing: {}", e),
            Ok(val) => assert_eq!(secret, val),
        }

    }

}
