use curve25519_dalek::scalar::Scalar;
use std::cmp::Ordering;

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
    for i in 0..abytes.len() {
        let o: Ordering = abytes[i].cmp(&bbytes[i]);
        if o != Ordering::Equal {
            return o;
        }
    }
    return Ordering::Equal;
}
