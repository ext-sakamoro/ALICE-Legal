//! C FFI for ALICE-Legal
//!
//! Provides 21 `extern "C"` functions for Unity / UE5 / native integration.
//!
//! License: MIT
//! Author: Moroya Sakamoto

use std::slice;

use crate::audit::{AuditEventKind, AuditLog};
use crate::contract::Contract;
use crate::procedure::{Procedure, StepKind};
use crate::statute::{ClauseKind, StatuteTree};

// ── ヘルパー ────────────────────────────────────────────────────────

/// `ClauseKind` を `u8` に変換する。
fn clause_kind_from_u8(v: u8) -> Option<ClauseKind> {
    match v {
        0 => Some(ClauseKind::Obligation),
        1 => Some(ClauseKind::Prohibition),
        2 => Some(ClauseKind::Permission),
        3 => Some(ClauseKind::Definition),
        4 => Some(ClauseKind::Penalty),
        5 => Some(ClauseKind::Exception),
        _ => None,
    }
}

/// `StepKind` を `u8` に変換する。
fn step_kind_from_u8(v: u8) -> Option<StepKind> {
    match v {
        0 => Some(StepKind::Application),
        1 => Some(StepKind::Review),
        2 => Some(StepKind::Approval),
        3 => Some(StepKind::Rejection),
        4 => Some(StepKind::Amendment),
        5 => Some(StepKind::Notification),
        6 => Some(StepKind::Completion),
        _ => None,
    }
}

/// `AuditEventKind` を `u8` に変換する。
fn audit_kind_from_u8(v: u8) -> Option<AuditEventKind> {
    match v {
        0 => Some(AuditEventKind::StatuteCreated),
        1 => Some(AuditEventKind::StatuteAmended),
        2 => Some(AuditEventKind::ContractCreated),
        3 => Some(AuditEventKind::ContractFulfilled),
        4 => Some(AuditEventKind::ContractBreached),
        5 => Some(AuditEventKind::ProcedureStarted),
        6 => Some(AuditEventKind::ProcedureCompleted),
        7 => Some(AuditEventKind::ProcedureRejected),
        _ => None,
    }
}

/// UTF-8スライスを安全に取得する。
unsafe fn str_from_raw<'a>(ptr: *const u8, len: u32) -> &'a str {
    if ptr.is_null() || len == 0 {
        ""
    } else {
        let bytes = slice::from_raw_parts(ptr, len as usize);
        std::str::from_utf8_unchecked(bytes)
    }
}

// ── StatuteTree (5) ─────────────────────────────────────────────────

/// 新しい `StatuteTree` を作成する。
///
/// # Safety
///
/// `title_ptr` は `title_len` バイトの有効なUTF-8メモリであること。
/// 戻り値は `alice_statute_destroy` で解放すること。
#[no_mangle]
pub unsafe extern "C" fn alice_statute_new(
    id: u64,
    title_ptr: *const u8,
    title_len: u32,
) -> *mut StatuteTree {
    let title = str_from_raw(title_ptr, title_len);
    Box::into_raw(Box::new(StatuteTree::new(id, title)))
}

/// 条項を追加し、割り当てられたIDを返す。
///
/// # Safety
///
/// `tree` は有効なポインタであること。
/// `content_ptr` は `content_len` バイトの有効なUTF-8メモリであること。
/// `parent_id` が 0 の場合は親なし。
#[no_mangle]
pub unsafe extern "C" fn alice_statute_add_clause(
    tree: *mut StatuteTree,
    kind: u8,
    content_ptr: *const u8,
    content_len: u32,
    parent_id: u64,
    effective_from_ns: u64,
) -> u64 {
    if tree.is_null() {
        return 0;
    }
    let kind = match clause_kind_from_u8(kind) {
        Some(k) => k,
        None => return 0,
    };
    let content = str_from_raw(content_ptr, content_len);
    let parent = if parent_id == 0 {
        None
    } else {
        Some(parent_id)
    };
    (*tree).add_clause(kind, content, parent, effective_from_ns)
}

/// 義務 (Obligation) 条項の数を返す。
///
/// # Safety
///
/// `tree` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_statute_obligations_count(tree: *const StatuteTree) -> u32 {
    if tree.is_null() {
        return 0;
    }
    (*tree).obligations().len() as u32
}

/// 条項が指定時刻に有効かどうかを返す。有効=1, 無効=0。
///
/// # Safety
///
/// `tree` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_statute_is_effective(
    tree: *const StatuteTree,
    clause_id: u64,
    at_ns: u64,
) -> u8 {
    if tree.is_null() {
        return 0;
    }
    u8::from((*tree).is_effective(clause_id, at_ns))
}

/// `StatuteTree` を解放する。
///
/// # Safety
///
/// `tree` は `alice_statute_new` で取得したポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_statute_destroy(tree: *mut StatuteTree) {
    if !tree.is_null() {
        drop(Box::from_raw(tree));
    }
}

// ── Contract (7) ────────────────────────────────────────────────────

/// 新しい `Contract` を作成する。
///
/// # Safety
///
/// `parties_ptr` は `parties_len` 個の `u64` の有効なメモリであること。
/// 戻り値は `alice_contract_destroy` で解放すること。
#[no_mangle]
pub unsafe extern "C" fn alice_contract_new(
    id: u64,
    parties_ptr: *const u64,
    parties_len: u32,
    created_ns: u64,
) -> *mut Contract {
    let parties = if parties_ptr.is_null() || parties_len == 0 {
        &[]
    } else {
        slice::from_raw_parts(parties_ptr, parties_len as usize)
    };
    Box::into_raw(Box::new(Contract::new(id, parties, created_ns)))
}

/// 債務を追加し、割り当てられたインデックスを返す。
///
/// # Safety
///
/// `contract` は有効なポインタであること。
/// `amount_ticks` は `i64` で渡す（FFI互換性のため i128 から縮小）。
#[no_mangle]
pub unsafe extern "C" fn alice_contract_add_obligation(
    contract: *mut Contract,
    debtor: u64,
    creditor: u64,
    amount_ticks: i64,
    due_ns: u64,
) -> u32 {
    if contract.is_null() {
        return u32::MAX;
    }
    (*contract).add_obligation(debtor, creditor, amount_ticks as i128, due_ns) as u32
}

/// 債務を履行済みにする。成功=1, 失敗=0。
///
/// # Safety
///
/// `contract` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_contract_fulfill_obligation(
    contract: *mut Contract,
    idx: u32,
) -> u8 {
    if contract.is_null() {
        return 0;
    }
    u8::from((*contract).fulfill_obligation(idx as usize))
}

/// ステータスを更新し、現在のステータスを返す。
///
/// 戻り値: Draft=0, Active=1, Fulfilled=2, Breached=3, Terminated=4, Expired=5
///
/// # Safety
///
/// `contract` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_contract_check_status(contract: *mut Contract, now_ns: u64) -> u8 {
    if contract.is_null() {
        return 0;
    }
    (*contract).check_status(now_ns);
    match (*contract).status {
        crate::contract::ContractStatus::Draft => 0,
        crate::contract::ContractStatus::Active => 1,
        crate::contract::ContractStatus::Fulfilled => 2,
        crate::contract::ContractStatus::Breached => 3,
        crate::contract::ContractStatus::Terminated => 4,
        crate::contract::ContractStatus::Expired => 5,
    }
}

/// 未履行の債務数を返す。
///
/// # Safety
///
/// `contract` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_contract_unfulfilled_count(contract: *const Contract) -> u32 {
    if contract.is_null() {
        return 0;
    }
    (*contract).unfulfilled_count() as u32
}

/// 全債務合計を `i64` で返す（i128 からの切り詰め）。
///
/// # Safety
///
/// `contract` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_contract_total_obligation_i64(contract: *const Contract) -> i64 {
    if contract.is_null() {
        return 0;
    }
    (*contract).total_obligation() as i64
}

/// `Contract` を解放する。
///
/// # Safety
///
/// `contract` は `alice_contract_new` で取得したポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_contract_destroy(contract: *mut Contract) {
    if !contract.is_null() {
        drop(Box::from_raw(contract));
    }
}

// ── Procedure (5) ───────────────────────────────────────────────────

/// 新しい `Procedure` を作成する。
///
/// # Safety
///
/// 戻り値は `alice_procedure_destroy` で解放すること。
#[no_mangle]
pub unsafe extern "C" fn alice_procedure_new(id: u64) -> *mut Procedure {
    Box::into_raw(Box::new(Procedure::new(id)))
}

/// 手続にステップを追加する。
///
/// # Safety
///
/// `proc` は有効なポインタであること。
/// `actor_ptr` / `content_ptr` は各 `_len` バイトの有効なUTF-8メモリであること。
/// `kind`: Application=0, Review=1, Approval=2, Rejection=3, Amendment=4, Notification=5, Completion=6
#[no_mangle]
pub unsafe extern "C" fn alice_procedure_add_step(
    proc_ptr: *mut Procedure,
    kind: u8,
    actor_ptr: *const u8,
    actor_len: u32,
    content_ptr: *const u8,
    content_len: u32,
    timestamp_ns: u64,
) {
    if proc_ptr.is_null() {
        return;
    }
    let kind = match step_kind_from_u8(kind) {
        Some(k) => k,
        None => return,
    };
    let actor = str_from_raw(actor_ptr, actor_len);
    let content = str_from_raw(content_ptr, content_len);
    (*proc_ptr).add_step(kind, actor, content, timestamp_ns);
}

/// ハッシュチェーンの整合性を検証する。有効=1, 無効=0。
///
/// # Safety
///
/// `proc` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_procedure_verify_chain(proc_ptr: *const Procedure) -> u8 {
    if proc_ptr.is_null() {
        return 0;
    }
    u8::from((*proc_ptr).verify_chain())
}

/// ステップ数を返す。
///
/// # Safety
///
/// `proc` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_procedure_step_count(proc_ptr: *const Procedure) -> u32 {
    if proc_ptr.is_null() {
        return 0;
    }
    (*proc_ptr).steps.len() as u32
}

/// `Procedure` を解放する。
///
/// # Safety
///
/// `proc` は `alice_procedure_new` で取得したポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_procedure_destroy(proc_ptr: *mut Procedure) {
    if !proc_ptr.is_null() {
        drop(Box::from_raw(proc_ptr));
    }
}

// ── AuditLog (4) ────────────────────────────────────────────────────

/// 新しい `AuditLog` を作成する。
///
/// # Safety
///
/// 戻り値は `alice_audit_destroy` で解放すること。
#[no_mangle]
pub unsafe extern "C" fn alice_audit_new() -> *mut AuditLog {
    Box::into_raw(Box::new(AuditLog::new()))
}

/// 監査エントリを追加し、シーケンス番号を返す。
///
/// # Safety
///
/// `log` は有効なポインタであること。
/// `actor_ptr` / `content_ptr` は各 `_len` バイトの有効なUTF-8メモリであること。
/// `kind`: StatuteCreated=0..ProcedureRejected=7
#[no_mangle]
pub unsafe extern "C" fn alice_audit_append(
    log: *mut AuditLog,
    kind: u8,
    entity_id: u64,
    actor_ptr: *const u8,
    actor_len: u32,
    content_ptr: *const u8,
    content_len: u32,
    timestamp_ns: u64,
) -> u64 {
    if log.is_null() {
        return u64::MAX;
    }
    let kind = match audit_kind_from_u8(kind) {
        Some(k) => k,
        None => return u64::MAX,
    };
    let actor = str_from_raw(actor_ptr, actor_len);
    let content = str_from_raw(content_ptr, content_len);
    (*log).append(kind, entity_id, actor, content, timestamp_ns)
}

/// 監査ログのエントリ数を返す。
///
/// # Safety
///
/// `log` は有効なポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_audit_len(log: *const AuditLog) -> u32 {
    if log.is_null() {
        return 0;
    }
    (*log).len() as u32
}

/// `AuditLog` を解放する。
///
/// # Safety
///
/// `log` は `alice_audit_new` で取得したポインタであること。
#[no_mangle]
pub unsafe extern "C" fn alice_audit_destroy(log: *mut AuditLog) {
    if !log.is_null() {
        drop(Box::from_raw(log));
    }
}

// ── テスト ──────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::ptr;

    #[test]
    fn test_statute_lifecycle() {
        unsafe {
            let title = b"Civil Code";
            let tree = alice_statute_new(1, title.as_ptr(), title.len() as u32);
            assert!(!tree.is_null());

            let content = b"Act in good faith";
            let id = alice_statute_add_clause(
                tree,
                0, // Obligation
                content.as_ptr(),
                content.len() as u32,
                0, // 親なし
                0,
            );
            assert!(id > 0);
            assert_eq!(alice_statute_obligations_count(tree), 1);
            assert_eq!(alice_statute_is_effective(tree, id, 0), 1);

            alice_statute_destroy(tree);
        }
    }

    #[test]
    fn test_contract_lifecycle() {
        unsafe {
            let parties = [1u64, 2];
            let contract =
                alice_contract_new(100, parties.as_ptr(), parties.len() as u32, 1_000_000);
            assert!(!contract.is_null());

            let idx = alice_contract_add_obligation(contract, 1, 2, 5000, 10_000_000_000);
            assert_ne!(idx, u32::MAX);
            assert_eq!(alice_contract_unfulfilled_count(contract), 1);
            assert_eq!(alice_contract_total_obligation_i64(contract), 5000);

            let ok = alice_contract_fulfill_obligation(contract, idx);
            assert_eq!(ok, 1);
            assert_eq!(alice_contract_unfulfilled_count(contract), 0);

            let status = alice_contract_check_status(contract, 5_000_000_000);
            assert_eq!(status, 2); // Fulfilled

            alice_contract_destroy(contract);
        }
    }

    #[test]
    fn test_procedure_lifecycle() {
        unsafe {
            let proc = alice_procedure_new(42);
            assert!(!proc.is_null());

            let actor = b"citizen-001";
            let content = b"permit application";
            alice_procedure_add_step(
                proc,
                0, // Application
                actor.as_ptr(),
                actor.len() as u32,
                content.as_ptr(),
                content.len() as u32,
                1_000_000_000,
            );
            assert_eq!(alice_procedure_step_count(proc), 1);
            assert_eq!(alice_procedure_verify_chain(proc), 1);

            alice_procedure_destroy(proc);
        }
    }

    #[test]
    fn test_audit_lifecycle() {
        unsafe {
            let log = alice_audit_new();
            assert!(!log.is_null());

            let actor = b"admin";
            let content = b"Civil Code enacted";
            let seq = alice_audit_append(
                log,
                0, // StatuteCreated
                1,
                actor.as_ptr(),
                actor.len() as u32,
                content.as_ptr(),
                content.len() as u32,
                0,
            );
            assert_eq!(seq, 0);
            assert_eq!(alice_audit_len(log), 1);

            alice_audit_destroy(log);
        }
    }

    #[test]
    fn test_null_safety() {
        unsafe {
            // StatuteTree
            assert_eq!(alice_statute_obligations_count(ptr::null()), 0);
            assert_eq!(alice_statute_is_effective(ptr::null(), 1, 0), 0);
            alice_statute_destroy(ptr::null_mut());

            // Contract
            assert_eq!(
                alice_contract_add_obligation(ptr::null_mut(), 1, 2, 100, 0),
                u32::MAX
            );
            assert_eq!(alice_contract_fulfill_obligation(ptr::null_mut(), 0), 0);
            assert_eq!(alice_contract_check_status(ptr::null_mut(), 0), 0);
            assert_eq!(alice_contract_unfulfilled_count(ptr::null()), 0);
            assert_eq!(alice_contract_total_obligation_i64(ptr::null()), 0);
            alice_contract_destroy(ptr::null_mut());

            // Procedure
            assert_eq!(alice_procedure_verify_chain(ptr::null()), 0);
            assert_eq!(alice_procedure_step_count(ptr::null()), 0);
            alice_procedure_destroy(ptr::null_mut());

            // AuditLog
            assert_eq!(
                alice_audit_append(ptr::null_mut(), 0, 1, ptr::null(), 0, ptr::null(), 0, 0),
                u64::MAX
            );
            assert_eq!(alice_audit_len(ptr::null()), 0);
            alice_audit_destroy(ptr::null_mut());
        }
    }

    #[test]
    fn test_invalid_kind_returns_zero() {
        unsafe {
            let title = b"Test";
            let tree = alice_statute_new(1, title.as_ptr(), title.len() as u32);
            let content = b"test";
            // kind=255 は無効
            let id =
                alice_statute_add_clause(tree, 255, content.as_ptr(), content.len() as u32, 0, 0);
            assert_eq!(id, 0);
            alice_statute_destroy(tree);

            let proc = alice_procedure_new(1);
            let actor = b"a";
            let cont = b"c";
            // kind=255 は無効 — 何も起きない
            alice_procedure_add_step(
                proc,
                255,
                actor.as_ptr(),
                actor.len() as u32,
                cont.as_ptr(),
                cont.len() as u32,
                0,
            );
            assert_eq!(alice_procedure_step_count(proc), 0);
            alice_procedure_destroy(proc);

            let log = alice_audit_new();
            // kind=255 は無効
            let seq = alice_audit_append(log, 255, 1, ptr::null(), 0, ptr::null(), 0, 0);
            assert_eq!(seq, u64::MAX);
            alice_audit_destroy(log);
        }
    }
}
