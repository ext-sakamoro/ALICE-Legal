//! Shared hashing utilities for ALICE-Legal.
//!
//! A single, canonical FNV-1a 64-bit implementation used by every module in
//! the crate.  All modules should call [`fnv1a`] from here rather than
//! maintaining their own copy.

/// FNV-1a 64-bit hash — inline, branchless, zero allocation.
///
/// Uses the standard FNV offset basis `0xcbf29ce484222325` and prime
/// `0x100000001b3`.
#[inline(always)]
pub fn fnv1a(data: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in data {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_input_returns_offset_basis() {
        assert_eq!(fnv1a(b""), 0xcbf29ce484222325);
    }

    #[test]
    fn test_known_hash_value() {
        // FNV-1a("hello") = 0xa430d84680aabd0b (well-known test vector)
        assert_eq!(fnv1a(b"hello"), 0xa430d84680aabd0b);
    }

    #[test]
    fn test_different_inputs_produce_different_hashes() {
        assert_ne!(fnv1a(b"alice"), fnv1a(b"bob"));
    }

    #[test]
    fn test_same_input_is_deterministic() {
        let h1 = fnv1a(b"deterministic");
        let h2 = fnv1a(b"deterministic");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_single_byte_inputs_differ() {
        // Every distinct single byte must produce a unique hash
        let h0 = fnv1a(&[0u8]);
        let h1 = fnv1a(&[1u8]);
        let hff = fnv1a(&[0xffu8]);
        assert_ne!(h0, h1);
        assert_ne!(h1, hff);
        assert_ne!(h0, hff);
    }

    #[test]
    fn test_order_matters() {
        // b"ab" and b"ba" must differ (FNV-1a is order-sensitive)
        assert_ne!(fnv1a(b"ab"), fnv1a(b"ba"));
    }

    #[test]
    fn test_all_zeros_nonzero() {
        // Even an all-zero input of non-trivial length must not return zero
        let result = fnv1a(&[0u8; 64]);
        assert_ne!(result, 0);
    }

    #[test]
    fn test_hash_nonzero_for_common_strings() {
        for s in &["contract", "statute", "procedure", "audit", "obligation"] {
            assert_ne!(fnv1a(s.as_bytes()), 0, "hash of '{}' must be nonzero", s);
        }
    }

    #[test]
    fn test_le_bytes_determinism() {
        // The hash of LE-encoded u64 bytes must be deterministic
        let val: u64 = 0xDEAD_BEEF_CAFE_1234;
        let h1 = fnv1a(&val.to_le_bytes());
        let h2 = fnv1a(&val.to_le_bytes());
        assert_eq!(h1, h2);
    }
}
