use curve25519_dalek::scalar::Scalar;
use std::cmp::Ordering;
use rand::{CryptoRng, RngCore};

/// Raise a Scalar to an arbitrary power.  This code is SUPER dumb: not efficient and not constant-time.
pub fn pow(x: &Scalar, p: usize) -> Scalar {
    if p == 0 {
        return Scalar::one();
    }

    let mut res = x.clone();
    for _ in 1..p {
        res *= x;
    }
    res
}

/// Compare two Scalar values.
pub fn compare_scalars(a: &Scalar, b: &Scalar) -> Ordering {
    let abytes = a.to_bytes();
    let bbytes = b.to_bytes();
    for _i in 0..abytes.len() {
        let i = abytes.len() - 1 - _i;
        let o: Ordering = abytes[i].cmp(&bbytes[i]);
        if o != Ordering::Equal {
            return o;
        }
    }
    return Ordering::Equal;
}

/// Get a Scalar distributed randomly across the possible values WITHOUT the highest bit of \ell being set.  That is,
/// whatever the highest 1-bit of \ell is, we ensure that every Scalar we hand back has that bit set to 0.  This 
/// ensures the values from this function, whenever XOR'd, will never go above \ell.
pub fn random_scalar<T>(rng: &mut T) -> Scalar
where
    T: RngCore + CryptoRng
{
    // each Scalar is 32 bytes
    let mut bytes = [0 as u8; 32];
    rng.fill_bytes(&mut bytes);

    // only the lower 4 bits of the final byte are significant, since we ignore the 5th
    bytes[31] &= 0x0f;
    Scalar::from_bits(bytes)
}

#[allow(unused_imports)]
mod tests {

    use curve25519_dalek::scalar::Scalar;
    use super::*;

    #[test]
    fn pow_easy() {
        for p in vec![0, 1, 2, 4] {
            let val = pow(&Scalar::one(), p);
            assert_eq!(Scalar::one(), val);
        };
    }

    #[test]
    fn pow_medium() {
        let val = pow(&Scalar::from(2u32), 2);
        assert_eq!(Scalar::from(4u32), val);

        let val = pow(&Scalar::from(8u32), 2);
        assert_eq!(Scalar::from(64u32), val);

        let val = pow(&Scalar::from(9u32), 3);
        assert_eq!(Scalar::from(729u32), val);
    }

    #[test]
    fn pow_overflow() {
        // in decimal, 5383850369160867882082008644310060803097890751578601301633528521931415479118
        let the_scalar = Scalar::from_canonical_bytes([78, 227, 105, 171, 173, 162, 96, 141, 241, 244, 32, 246, 255, 9, 210, 32, 110, 245, 179, 133, 8, 34, 83, 32, 220, 162, 102, 9, 189, 38, 231, 11]).unwrap();

        // in decimal, 905024118957487278709981156877405425812244224552873609041215153919592868854
        let the_answer = Scalar::from_canonical_bytes([246, 171, 1, 72, 68, 73, 121, 162, 178, 134, 163, 34, 136, 171, 117, 234, 5, 196, 64, 75, 61, 139, 40, 49, 68, 126, 27, 73, 186, 57, 0, 2]).unwrap();
        let val = pow(&the_scalar, 32);
        assert_eq!(the_answer, val);
    }

    #[test]
    fn compare_eq() {
        let one = Scalar::from_canonical_bytes([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(Ordering::Equal, compare_scalars(&Scalar::zero(), &Scalar::zero()));
        assert_eq!(Ordering::Equal, compare_scalars(&Scalar::one(), &Scalar::from(1u32)));
        assert_eq!(Ordering::Equal, compare_scalars(&Scalar::from(1u32), &one.unwrap()));
    }

    #[test]
    fn compare_lt_easy() {
        assert_eq!(Ordering::Less, compare_scalars(&Scalar::zero(), &Scalar::one()));
    }
    
    #[test]
    fn compare_lt_medium() {
        let smaller = Scalar::from_canonical_bytes([246, 171, 1,    72,  68,  73, 121, 162, 178, 134, 163,  34, 136, 171, 117, 234,   5, 196,  64,  75, 61, 139, 40, 49,  68, 126,  27, 73, 186, 57,   0, 2]).unwrap();
        let larger = Scalar::from_canonical_bytes([  78, 227, 105, 171, 173, 162,  96, 141, 241, 244,  32, 246, 255,   9, 210,  32, 110, 245, 179, 133,  8,  34, 83, 32, 220, 162, 102,  9, 189, 38, 231, 11]).unwrap();
        assert_eq!(Ordering::Less, compare_scalars(&smaller, &larger));
    }

    #[test]
    fn compare_gt_easy() {
        assert_eq!(Ordering::Greater, compare_scalars(&Scalar::one(), &Scalar::zero()));
    }

    #[test]
    fn compare_gt_medium() {
        let smaller = Scalar::from_canonical_bytes([246, 171, 1, 72, 68, 73, 121, 162, 178, 134, 163, 34, 136, 171, 117, 234, 5, 196, 64, 75, 61, 139, 40, 49, 68, 126, 27, 73, 186, 57, 0, 2]).unwrap();
        let larger = Scalar::from_canonical_bytes([78, 227, 105, 171, 173, 162, 96, 141, 241, 244, 32, 246, 255, 9, 210, 32, 110, 245, 179, 133, 8, 34, 83, 32, 220, 162, 102, 9, 189, 38, 231, 11]).unwrap();
        assert_eq!(Ordering::Greater, compare_scalars(&larger, &smaller));
    }
}