//! # ALICE-Legal
//!
//! Deterministic legal tree compilation, contract execution, and
//! administrative procedure events for machine-verifiable legal operations.
//!
//! ## Modules
//!
//! - [`statute`] — Natural language laws compiled into deterministic AST-based legal trees
//! - [`contract`] — Smart contract-like deterministic contract execution
//! - [`procedure`] — Administrative procedures as tamper-evident event streams
//! - [`audit`] — Immutable audit trail for all legal operations
//!
//! ## Example
//!
//! ```rust
//! use alice_legal::statute::{StatuteTree, ClauseKind};
//! use alice_legal::contract::Contract;
//! use alice_legal::procedure::Procedure;
//! use alice_legal::audit::{AuditLog, AuditEventKind};
//!
//! // Build a statute tree
//! let mut statute = StatuteTree::new(1, "Civil Code Article 1");
//! let clause_id = statute.add_clause(
//!     ClauseKind::Obligation,
//!     "Parties must act in good faith",
//!     None,
//!     0,
//! );
//! assert_eq!(statute.obligations().len(), 1);
//!
//! // Create a contract between two parties
//! let mut contract = Contract::new(100, &[1, 2], 1_000_000);
//! contract.add_obligation(1, 2, 5000_0000, 2_000_000);
//! assert_eq!(contract.unfulfilled_count(), 1);
//!
//! // Start an administrative procedure
//! let mut proc = Procedure::new(42);
//! use alice_legal::procedure::StepKind;
//! proc.add_step(StepKind::Application, "citizen-001", "permit application", 1_000_000);
//! assert!(proc.verify_chain());
//!
//! // Record to audit log
//! let mut log = AuditLog::new();
//! log.append(AuditEventKind::StatuteCreated, 1, "admin", "Civil Code Article 1", 0);
//! assert_eq!(log.len(), 1);
//! ```

pub mod audit;
pub mod contract;
pub mod procedure;
pub mod statute;

pub use audit::{AuditEntry, AuditEventKind, AuditLog};
pub use contract::{Contract, ContractId, ContractStatus, Obligation as ContractObligation, PartyId};
pub use procedure::{Procedure, ProcedureId, ProcedureStatus, ProcedureStep, StepKind};
pub use statute::{Clause, ClauseKind, StatuteId, StatuteTree};
