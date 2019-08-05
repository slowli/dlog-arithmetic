use curve25519::{
    constants::ED25519_BASEPOINT_POINT,
    edwards::{CompressedEdwardsY, EdwardsPoint},
    scalar::Scalar,
    traits::Identity,
};
use failure::Fail;
use std::{convert::TryInto, ops};

/// Finite prime-order group.
pub trait Group: Clone + 'static {
    /// Scalar type.
    type Scalar: Copy
        + Default
        + PartialEq
        + ops::Neg<Output = Self::Scalar>
        + ops::Add<Output = Self::Scalar>
        + ops::Sub<Output = Self::Scalar>
        + ops::Mul<Output = Self::Scalar>;

    /// Group element.
    type Element: Copy
        + Default
        + PartialEq
        + ops::Add<Output = Self::Element>
        + ops::Sub<Output = Self::Element>
        + for<'a> ops::Mul<&'a Self::Scalar, Output = Self::Element>;

    /// Error for fallible operations.
    type Error: 'static + Fail;

    /// Converts an integer into a scalar.
    fn scalar_from_u64(&self, value: u64) -> Result<Self::Scalar, Self::Error>;
    /// Converts bytes into a scalar. This should fail if `bytes` does not correspond
    /// to a valid scalar presentation.
    fn scalar_from_bytes(&self, bytes: &[u8]) -> Result<Self::Scalar, Self::Error>;
    /// Converts scalar to a serialized form.
    fn scalar_to_bytes(scalar: Self::Scalar) -> Vec<u8>;
    /// Inverts scalar. `None` should be returned if `scalar` equals 0.
    fn invert_scalar(&self, scalar: Self::Scalar) -> Option<Self::Scalar>;

    /// Converts bytes into a group element. This should fail if `bytes` does not correspond
    /// to a valid element presentation.
    fn element_from_bytes(&self, bytes: &[u8]) -> Result<Self::Element, Self::Error>;
    /// Converts group element to a serialized form.
    fn element_to_bytes(element: Self::Element) -> Vec<u8>;
    /// Returns the identity element of the group.
    fn identity_element(&self) -> Self::Element;
    /// Returns the basepoint of the group (i.e., the "standard" group generator).
    fn base_element(&self) -> Self::Element;
}

/// Prime-order elliptic curve group used in Ed25519 signature scheme.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ed25519;

/// `Ed25519` errors.
#[derive(Debug, Fail, PartialEq)]
pub enum Ed25519Error {
    /// Invalid byte size for a scalar.
    #[fail(display = "Invalid byte size for a scalar; 32 expected")]
    InvalidScalarSize,

    /// Invalid byte size for a point.
    #[fail(display = "Invalid byte size for a point; 32 expected")]
    InvalidPointSize,

    /// Scalar is not canonical, i.e., exceeds the group order.
    #[fail(display = "Non-canonical scalar")]
    NonCanonicalScalar,

    /// Bytes cannot be deserialized as a compressed Curve25519 point.
    #[fail(display = "Not a point on Curve25519")]
    NotAPoint,

    /// Curve25519 point obtained after deserialization does not lie in the prime-order
    /// subgroup.
    #[fail(display = "Point has a torsion component")]
    PointWithTorsion,
}

impl Group for Ed25519 {
    type Scalar = Scalar;
    type Element = EdwardsPoint;
    type Error = Ed25519Error;

    fn scalar_from_u64(&self, value: u64) -> Result<Self::Scalar, Self::Error> {
        Ok(Scalar::from(value))
    }

    fn scalar_from_bytes(&self, bytes: &[u8]) -> Result<Self::Scalar, Self::Error> {
        let bytes: [u8; 32] = bytes
            .try_into()
            .map_err(|_| Ed25519Error::InvalidScalarSize)?;
        Scalar::from_canonical_bytes(bytes).ok_or(Ed25519Error::NonCanonicalScalar)
    }

    fn scalar_to_bytes(scalar: Self::Scalar) -> Vec<u8> {
        scalar.as_bytes().to_vec()
    }

    fn invert_scalar(&self, scalar: Self::Scalar) -> Option<Self::Scalar> {
        if scalar == Scalar::zero() {
            None
        } else {
            Some(scalar.invert())
        }
    }

    fn element_from_bytes(&self, bytes: &[u8]) -> Result<Self::Element, Self::Error> {
        if bytes.len() != 32 {
            return Err(Ed25519Error::InvalidPointSize);
        }
        let point = CompressedEdwardsY::from_slice(bytes)
            .decompress()
            .ok_or(Ed25519Error::NotAPoint)?;
        if !point.is_torsion_free() {
            return Err(Ed25519Error::PointWithTorsion);
        }
        Ok(point)
    }

    fn element_to_bytes(element: Self::Element) -> Vec<u8> {
        element.compress().as_bytes().to_vec()
    }

    fn identity_element(&self) -> Self::Element {
        EdwardsPoint::identity()
    }

    fn base_element(&self) -> Self::Element {
        ED25519_BASEPOINT_POINT
    }
}
