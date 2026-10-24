//! Identifiers of ALICE-Legal records: LawIdHasher v2 (alice-zip), 32 bytes.
//!
//! Every content, identity and chain field of a record is the v2 law identifier of what it names:
//! a kind that tells the record and the field apart (`alice-legal/<record>/<field>/v1`), the
//! semantics [`LEGAL_SEMANTICS_ID`], then the values, typed (a string is a `str`, an integer a
//! `u64`, another identifier an `id`), each with its length. Two different inputs give two
//! different identifiers unless SHA-256 collides.
//!
//! Author: Moroya Sakamoto

use alice_zip::law_id::LawIdHasher;

/// A record identifier: 32 bytes
pub type Digest = [u8; 32];

/// The identifier of nothing: the link of the first step of a chain
pub const ZERO: Digest = [0; 32];

/// The semantics of every ALICE-Legal identifier: text and integers only, no arithmetic.
/// `sha256(b"alice-legal/semantics/text-and-integers/v1")`
pub const LEGAL_SEMANTICS_ID: [u8; 32] = [
    0xd4, 0x8c, 0xe4, 0x2c, 0x2e, 0xa1, 0x5a, 0xab, 0x42, 0xbc, 0xa8, 0x0e, 0x47, 0x75, 0x30, 0x99,
    0xfd, 0x47, 0xfe, 0x90, 0x40, 0x09, 0xa9, 0xf3, 0x8c, 0x42, 0xe2, 0xe2, 0x82, 0xc8, 0xf0, 0xe2,
];

/// A hasher for one field of one record
#[must_use]
pub fn hasher(kind: &str) -> LawIdHasher {
    LawIdHasher::new(kind.as_bytes(), &LEGAL_SEMANTICS_ID)
}

/// The identifier of a text field
#[must_use]
pub fn text(kind: &str, value: &str) -> Digest {
    hasher(kind).str(value).finish()
}

/// The identifier of a byte payload
#[must_use]
pub fn data(kind: &str, value: &[u8]) -> Digest {
    hasher(kind).bytes(value).finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_semantics_is_the_named_constant() {
        let h = alice_sign::hash_data(b"alice-legal/semantics/text-and-integers/v1");
        assert_eq!(LEGAL_SEMANTICS_ID, h.0);
    }

    #[test]
    fn the_kind_and_the_type_take_part() {
        assert_ne!(text("alice-legal/a/v1", "x"), text("alice-legal/b/v1", "x"));
        assert_ne!(
            text("alice-legal/a/v1", "x"),
            data("alice-legal/a/v1", b"x")
        );
        assert_ne!(text("alice-legal/a/v1", "x"), ZERO);
    }
}
