//! Convenience re-export (= `use alice_legal::prelude::*;` で主要 API 一括取得)
//!
//! Legal 系 4 core module (statute / contract / procedure / audit) +
//! `signed_contract` (RFC 3161 統合) の主要型を prelude 経由で提供する
//! `dispute` / `hash_utils` / `oracle` / `penalty` / `ffi` (feature-gated)
//! は補助 module のため prelude 非対象

pub use crate::audit::{AuditEntry, AuditEventKind, AuditLog};
pub use crate::contract::{
    Contract, ContractId, ContractStatus, Obligation as ContractObligation, PartyId,
};
pub use crate::procedure::{Procedure, ProcedureId, ProcedureStatus, ProcedureStep, StepKind};
pub use crate::signed_contract::{ContractLog, ContractRecord, SignedContract};
pub use crate::statute::{Clause, ClauseKind, StatuteId, StatuteTree};
