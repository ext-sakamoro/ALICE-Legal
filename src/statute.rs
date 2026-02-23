//! Legal statute representation as a deterministic AST-based legal tree.
//!
//! Statutes are compiled into a tree of [`Clause`] nodes identified by
//! auto-incrementing IDs. Content is stored as FNV-1a hashes, keeping the
//! structure lightweight and tamper-detectable.
//!
//! Two internal `HashMap` indices are maintained on every [`StatuteTree`] to
//! replace O(n) linear scans with O(1) lookups:
//!
//! - `clause_index: HashMap<clause_id, Vec_index>` — used by [`find_clause`](StatuteTree::find_clause).
//! - `children_index: HashMap<parent_id, Vec<Vec_index>>` — used by [`children_of`](StatuteTree::children_of).

use std::collections::HashMap;

use crate::hash_utils::fnv1a;

/// Unique identifier for a statute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StatuteId(pub u64);

/// The legal nature of a clause within a statute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClauseKind {
    /// A duty imposed on a subject.
    Obligation,
    /// An act that is forbidden.
    Prohibition,
    /// An act that is allowed.
    Permission,
    /// A term defined for use elsewhere in the statute.
    Definition,
    /// A sanction for non-compliance.
    Penalty,
    /// A carve-out from another clause.
    Exception,
}

/// A single node in the legal AST.
#[derive(Debug, Clone)]
pub struct Clause {
    /// Unique clause identifier within this statute (auto-incrementing).
    pub id: u64,
    /// The legal nature of this clause.
    pub kind: ClauseKind,
    /// Optional parent clause id for nested structures.
    pub parent_id: Option<u64>,
    /// FNV-1a hash of the clause's natural-language content.
    pub content_hash: u64,
    /// Unix-epoch nanosecond timestamp at which this clause becomes effective.
    pub effective_from_ns: u64,
    /// Optional expiry timestamp (exclusive). `None` means no expiry.
    pub expires_ns: Option<u64>,
}

/// A complete statute compiled into a deterministic legal tree.
///
/// Internal HashMap indices keep [`find_clause`](StatuteTree::find_clause) and
/// [`children_of`](StatuteTree::children_of) at O(1) amortised cost rather than
/// the O(n) linear scan that a plain `Vec` would require.
#[derive(Debug, Clone)]
pub struct StatuteTree {
    /// The statute's unique identifier.
    pub id: StatuteId,
    /// FNV-1a hash of the statute's title string.
    pub title_hash: u64,
    /// All clauses in document order.
    pub clauses: Vec<Clause>,
    /// Monotonically increasing version counter; incremented on each amendment.
    pub version: u32,
    /// Internal counter for assigning clause IDs.
    next_clause_id: u64,
    /// HashMap index: clause_id -> index into `clauses`.
    clause_index: HashMap<u64, usize>,
    /// HashMap index: parent_id -> list of indices into `clauses`.
    children_index: HashMap<u64, Vec<usize>>,
}

impl StatuteTree {
    /// Create a new, empty statute tree.
    ///
    /// # Arguments
    ///
    /// * `id` — Numeric statute identifier.
    /// * `title` — Human-readable title; stored as FNV-1a hash.
    pub fn new(id: u64, title: &str) -> Self {
        Self {
            id: StatuteId(id),
            title_hash: fnv1a(title.as_bytes()),
            clauses: Vec::new(),
            version: 1,
            next_clause_id: 1,
            clause_index: HashMap::new(),
            children_index: HashMap::new(),
        }
    }

    /// Add a clause to this statute and return its auto-assigned id.
    ///
    /// # Arguments
    ///
    /// * `kind` — Legal nature of the clause.
    /// * `content` — Natural-language text; stored as FNV-1a hash.
    /// * `parent_id` — Optional parent clause for nesting.
    /// * `effective_from_ns` — Nanosecond timestamp when the clause takes effect.
    pub fn add_clause(
        &mut self,
        kind: ClauseKind,
        content: &str,
        parent_id: Option<u64>,
        effective_from_ns: u64,
    ) -> u64 {
        let id = self.next_clause_id;
        self.next_clause_id += 1;
        let vec_idx = self.clauses.len();
        self.clauses.push(Clause {
            id,
            kind,
            parent_id,
            content_hash: fnv1a(content.as_bytes()),
            effective_from_ns,
            expires_ns: None,
        });
        // Update the clause_id -> Vec index map.
        self.clause_index.insert(id, vec_idx);
        // Update the parent_id -> children map.
        if let Some(pid) = parent_id {
            self.children_index.entry(pid).or_default().push(vec_idx);
        }
        id
    }

    /// Find a clause by its id.
    ///
    /// Uses the internal HashMap index for O(1) lookup instead of an O(n)
    /// linear scan.
    pub fn find_clause(&self, id: u64) -> Option<&Clause> {
        self.clause_index.get(&id).map(|&i| &self.clauses[i])
    }

    /// Return all direct children of a given parent clause id.
    ///
    /// Uses the internal HashMap index for O(1) lookup instead of an O(n)
    /// linear scan.
    pub fn children_of(&self, parent_id: u64) -> Vec<&Clause> {
        match self.children_index.get(&parent_id) {
            None => Vec::new(),
            Some(indices) => indices.iter().map(|&i| &self.clauses[i]).collect(),
        }
    }

    /// Return all clauses of kind [`ClauseKind::Obligation`].
    pub fn obligations(&self) -> Vec<&Clause> {
        self.clauses
            .iter()
            .filter(|c| c.kind == ClauseKind::Obligation)
            .collect()
    }

    /// Check whether a clause is in effect at a given nanosecond timestamp.
    ///
    /// Returns `false` if the clause does not exist, has not yet taken effect,
    /// or has already expired.
    pub fn is_effective(&self, clause_id: u64, at_ns: u64) -> bool {
        match self.find_clause(clause_id) {
            None => false,
            Some(c) => {
                if at_ns < c.effective_from_ns {
                    return false;
                }
                if let Some(exp) = c.expires_ns {
                    if at_ns >= exp {
                        return false;
                    }
                }
                true
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper: one second in nanoseconds
    const NS: u64 = 1_000_000_000;

    #[test]
    fn test_create_and_add_clauses() {
        let mut tree = StatuteTree::new(1, "Civil Code");
        let id1 = tree.add_clause(ClauseKind::Obligation, "Act in good faith", None, 0);
        let id2 = tree.add_clause(ClauseKind::Prohibition, "Do not defraud", None, 0);
        let id3 = tree.add_clause(ClauseKind::Permission, "May assign rights", None, 0);
        assert_eq!(tree.clauses.len(), 3);
        assert_eq!(id1, 1);
        assert_eq!(id2, 2);
        assert_eq!(id3, 3);
    }

    #[test]
    fn test_find_clause_by_id() {
        let mut tree = StatuteTree::new(2, "Tax Code");
        let id = tree.add_clause(ClauseKind::Obligation, "Pay income tax annually", None, 0);
        let clause = tree.find_clause(id).expect("clause must exist");
        assert_eq!(clause.id, id);
        assert_eq!(clause.kind, ClauseKind::Obligation);
        assert!(tree.find_clause(9999).is_none());
    }

    #[test]
    fn test_children_of_parent() {
        let mut tree = StatuteTree::new(3, "Administrative Code");
        let parent = tree.add_clause(ClauseKind::Definition, "Section 1", None, 0);
        let child1 = tree.add_clause(ClauseKind::Obligation, "Sub-clause A", Some(parent), 0);
        let child2 = tree.add_clause(ClauseKind::Prohibition, "Sub-clause B", Some(parent), 0);
        // Unrelated clause
        tree.add_clause(ClauseKind::Permission, "Other section", None, 0);

        let children = tree.children_of(parent);
        assert_eq!(children.len(), 2);
        let child_ids: Vec<u64> = children.iter().map(|c| c.id).collect();
        assert!(child_ids.contains(&child1));
        assert!(child_ids.contains(&child2));
    }

    #[test]
    fn test_filter_obligations() {
        let mut tree = StatuteTree::new(4, "Criminal Code");
        tree.add_clause(ClauseKind::Obligation, "Report income", None, 0);
        tree.add_clause(ClauseKind::Prohibition, "Do not steal", None, 0);
        tree.add_clause(ClauseKind::Obligation, "Appear in court", None, 0);
        tree.add_clause(ClauseKind::Penalty, "Fine for theft", None, 0);
        tree.add_clause(
            ClauseKind::Obligation,
            "Pay penalty within 30 days",
            None,
            0,
        );

        let obs = tree.obligations();
        assert_eq!(obs.len(), 3);
        assert!(obs.iter().all(|c| c.kind == ClauseKind::Obligation));
    }

    #[test]
    fn test_is_effective_timing() {
        let mut tree = StatuteTree::new(5, "Temporal Act");
        let id = tree.add_clause(
            ClauseKind::Obligation,
            "Effective clause",
            None,
            10 * NS, // effective from 10s
        );
        // Set expiry directly for test
        tree.clauses.last_mut().unwrap().expires_ns = Some(20 * NS);

        // Before effective date
        assert!(!tree.is_effective(id, 5 * NS));
        // At effective date
        assert!(tree.is_effective(id, 10 * NS));
        // During effective period
        assert!(tree.is_effective(id, 15 * NS));
        // At expiry (exclusive)
        assert!(!tree.is_effective(id, 20 * NS));
        // After expiry
        assert!(!tree.is_effective(id, 25 * NS));
        // Non-existent clause
        assert!(!tree.is_effective(9999, 15 * NS));
    }

    #[test]
    fn test_content_hash_is_deterministic() {
        let mut t1 = StatuteTree::new(6, "Hash Test");
        let mut t2 = StatuteTree::new(6, "Hash Test");

        let id1 = t1.add_clause(ClauseKind::Definition, "term: natural person", None, 0);
        let id2 = t2.add_clause(ClauseKind::Definition, "term: natural person", None, 0);

        let h1 = t1.find_clause(id1).unwrap().content_hash;
        let h2 = t2.find_clause(id2).unwrap().content_hash;
        assert_eq!(h1, h2);

        // Different content must produce a different hash
        let mut t3 = StatuteTree::new(6, "Hash Test");
        let id3 = t3.add_clause(ClauseKind::Definition, "term: legal entity", None, 0);
        let h3 = t3.find_clause(id3).unwrap().content_hash;
        assert_ne!(h1, h3);
    }

    #[test]
    fn test_title_hash_nonzero() {
        let tree = StatuteTree::new(10, "Commercial Code");
        assert_ne!(tree.title_hash, 0);
    }

    #[test]
    fn test_different_titles_produce_different_hashes() {
        let t1 = StatuteTree::new(11, "Civil Code");
        let t2 = StatuteTree::new(11, "Criminal Code");
        assert_ne!(t1.title_hash, t2.title_hash);
    }

    #[test]
    fn test_statute_id_wraps_raw_value() {
        let tree = StatuteTree::new(42, "Some Act");
        assert_eq!(tree.id, StatuteId(42));
        // StatuteId public field
        assert_eq!(tree.id.0, 42);
    }

    #[test]
    fn test_new_tree_starts_at_version_1() {
        let tree = StatuteTree::new(1, "Test Act");
        assert_eq!(tree.version, 1);
        assert!(tree.clauses.is_empty());
    }

    #[test]
    fn test_all_clause_kinds_can_be_added() {
        let mut tree = StatuteTree::new(20, "Full Kind Test");
        let kinds = [
            ClauseKind::Obligation,
            ClauseKind::Prohibition,
            ClauseKind::Permission,
            ClauseKind::Definition,
            ClauseKind::Penalty,
            ClauseKind::Exception,
        ];
        for kind in kinds {
            let id = tree.add_clause(kind, "content", None, 0);
            let clause = tree.find_clause(id).unwrap();
            assert_eq!(clause.kind, kind);
        }
        assert_eq!(tree.clauses.len(), 6);
    }

    #[test]
    fn test_children_of_nonexistent_parent_returns_empty() {
        let tree = StatuteTree::new(30, "Empty Tree");
        let children = tree.children_of(999);
        assert!(children.is_empty());
    }

    #[test]
    fn test_find_clause_missing_returns_none() {
        let tree = StatuteTree::new(31, "Empty Tree");
        assert!(tree.find_clause(0).is_none());
        assert!(tree.find_clause(u64::MAX).is_none());
    }

    #[test]
    fn test_obligations_empty_when_no_obligations() {
        let mut tree = StatuteTree::new(32, "No Obligations Act");
        tree.add_clause(ClauseKind::Prohibition, "No speeding", None, 0);
        tree.add_clause(ClauseKind::Penalty, "Fine", None, 0);
        assert!(tree.obligations().is_empty());
    }

    #[test]
    fn test_is_effective_no_expiry() {
        let mut tree = StatuteTree::new(33, "Perpetual Act");
        let id = tree.add_clause(ClauseKind::Obligation, "Perpetual duty", None, 5 * NS);
        // Before effective date
        assert!(!tree.is_effective(id, 4 * NS));
        // At and after effective date — no expiry, stays effective forever
        assert!(tree.is_effective(id, 5 * NS));
        assert!(tree.is_effective(id, u64::MAX));
    }

    #[test]
    fn test_clause_ids_are_auto_incrementing_from_1() {
        let mut tree = StatuteTree::new(34, "Sequence Test");
        for expected in 1u64..=10 {
            let id = tree.add_clause(ClauseKind::Permission, "allow something", None, 0);
            assert_eq!(id, expected);
        }
    }

    #[test]
    fn test_content_hash_nonzero_for_all_kinds() {
        let mut tree = StatuteTree::new(35, "Hash Nonzero Test");
        let id = tree.add_clause(ClauseKind::Exception, "carved-out case", None, 0);
        let clause = tree.find_clause(id).unwrap();
        assert_ne!(clause.content_hash, 0);
    }

    #[test]
    fn test_multi_level_parent_child_nesting() {
        let mut tree = StatuteTree::new(40, "Nested Code");
        let root = tree.add_clause(ClauseKind::Definition, "Chapter 1", None, 0);
        let section = tree.add_clause(ClauseKind::Definition, "Section 1.1", Some(root), 0);
        let leaf = tree.add_clause(ClauseKind::Obligation, "Leaf obligation", Some(section), 0);

        // Root has one child: section
        let root_children = tree.children_of(root);
        assert_eq!(root_children.len(), 1);
        assert_eq!(root_children[0].id, section);

        // Section has one child: leaf
        let section_children = tree.children_of(section);
        assert_eq!(section_children.len(), 1);
        assert_eq!(section_children[0].id, leaf);

        // Leaf has no children
        assert!(tree.children_of(leaf).is_empty());
    }

    #[test]
    fn test_effective_from_zero_is_immediately_effective() {
        let mut tree = StatuteTree::new(41, "Immediate Act");
        let id = tree.add_clause(ClauseKind::Obligation, "Immediate", None, 0);
        assert!(tree.is_effective(id, 0));
        assert!(tree.is_effective(id, 1));
    }
}
