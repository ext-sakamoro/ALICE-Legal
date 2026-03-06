//! Penalty Execution — 違反時のペナルティ自動発動。
//!
//! 契約違反を検出し、ペナルティスケジュールに従って
//! 自動的にペナルティを適用する。

use crate::contract::{ContractId, PartyId};
use crate::hash_utils::fnv1a;

/// ペナルティ種別。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PenaltyKind {
    /// 固定金額ペナルティ。
    FixedAmount,
    /// 日割り遅延金。
    DailyLateFee,
    /// 契約解除。
    Termination,
    /// 一時停止。
    Suspension,
    /// 警告。
    Warning,
}

/// ペナルティ状態。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PenaltyStatus {
    /// 待機中 (未発動)。
    Pending,
    /// 発動済み。
    Executed,
    /// 免除。
    Waived,
    /// 係争中。
    Disputed,
}

/// ペナルティ定義。
#[derive(Debug, Clone)]
pub struct PenaltyRule {
    /// ルール ID。
    pub id: u64,
    /// 対象契約。
    pub contract_id: ContractId,
    /// 対象義務インデックス。
    pub obligation_index: usize,
    /// ペナルティ種別。
    pub kind: PenaltyKind,
    /// 金額 (ticks)。
    pub amount_ticks: i128,
    /// 猶予期間 (ナノ秒)。
    pub grace_period_ns: u64,
    /// 最大適用回数 (0 = 無制限)。
    pub max_applications: u32,
}

/// 適用済みペナルティ記録。
#[derive(Debug, Clone)]
pub struct PenaltyRecord {
    /// ルール ID。
    pub rule_id: u64,
    /// 対象当事者。
    pub party: PartyId,
    /// 金額 (ticks)。
    pub amount_ticks: i128,
    /// 適用時刻。
    pub applied_ns: u64,
    /// 状態。
    pub status: PenaltyStatus,
    /// 記録ハッシュ。
    pub record_hash: u64,
}

/// ペナルティエンジン。
#[derive(Debug)]
pub struct PenaltyEngine {
    /// ペナルティルール。
    rules: Vec<PenaltyRule>,
    /// 適用記録。
    records: Vec<PenaltyRecord>,
}

impl PenaltyEngine {
    /// 新しいペナルティエンジンを作成。
    #[must_use]
    pub const fn new() -> Self {
        Self {
            rules: Vec::new(),
            records: Vec::new(),
        }
    }

    /// ペナルティルールを追加。
    pub fn add_rule(&mut self, rule: PenaltyRule) {
        self.rules.push(rule);
    }

    /// 義務違反に対するペナルティを発動。
    pub fn execute_penalty(&mut self, rule_id: u64, party: PartyId, now_ns: u64) -> Option<usize> {
        let rule = self.rules.iter().find(|r| r.id == rule_id)?;

        // 最大適用回数チェック
        if rule.max_applications > 0 {
            let applied = self
                .records
                .iter()
                .filter(|r| r.rule_id == rule_id && r.status == PenaltyStatus::Executed)
                .count() as u32;
            if applied >= rule.max_applications {
                return None;
            }
        }

        let mut hash_data = rule_id.to_le_bytes().to_vec();
        hash_data.extend_from_slice(&party.0.to_le_bytes());
        hash_data.extend_from_slice(&now_ns.to_le_bytes());

        let record = PenaltyRecord {
            rule_id,
            party,
            amount_ticks: rule.amount_ticks,
            applied_ns: now_ns,
            status: PenaltyStatus::Executed,
            record_hash: fnv1a(&hash_data),
        };
        self.records.push(record);
        Some(self.records.len() - 1)
    }

    /// ペナルティを免除。
    pub fn waive_penalty(&mut self, record_index: usize) -> bool {
        if let Some(r) = self.records.get_mut(record_index) {
            r.status = PenaltyStatus::Waived;
            true
        } else {
            false
        }
    }

    /// ペナルティを係争状態に変更。
    pub fn dispute_penalty(&mut self, record_index: usize) -> bool {
        if let Some(r) = self.records.get_mut(record_index) {
            r.status = PenaltyStatus::Disputed;
            true
        } else {
            false
        }
    }

    /// ルール数。
    #[must_use]
    pub const fn rule_count(&self) -> usize {
        self.rules.len()
    }

    /// 記録数。
    #[must_use]
    pub const fn record_count(&self) -> usize {
        self.records.len()
    }

    /// 当事者の累計ペナルティ金額。
    #[must_use]
    pub fn total_penalty_for(&self, party: PartyId) -> i128 {
        self.records
            .iter()
            .filter(|r| r.party == party && r.status == PenaltyStatus::Executed)
            .map(|r| r.amount_ticks)
            .sum()
    }

    /// 記録を取得。
    #[must_use]
    pub fn get_record(&self, index: usize) -> Option<&PenaltyRecord> {
        self.records.get(index)
    }
}

impl Default for PenaltyEngine {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_rule(id: u64, kind: PenaltyKind, amount: i128) -> PenaltyRule {
        PenaltyRule {
            id,
            contract_id: ContractId(1),
            obligation_index: 0,
            kind,
            amount_ticks: amount,
            grace_period_ns: 0,
            max_applications: 0,
        }
    }

    #[test]
    fn empty_engine() {
        let e = PenaltyEngine::new();
        assert_eq!(e.rule_count(), 0);
        assert_eq!(e.record_count(), 0);
    }

    #[test]
    fn add_rule() {
        let mut e = PenaltyEngine::new();
        e.add_rule(make_rule(1, PenaltyKind::FixedAmount, 1000));
        assert_eq!(e.rule_count(), 1);
    }

    #[test]
    fn execute_penalty() {
        let mut e = PenaltyEngine::new();
        e.add_rule(make_rule(1, PenaltyKind::FixedAmount, 5000));
        let idx = e.execute_penalty(1, PartyId(10), 1_000_000).unwrap();
        assert_eq!(e.record_count(), 1);
        let r = e.get_record(idx).unwrap();
        assert_eq!(r.amount_ticks, 5000);
        assert_eq!(r.status, PenaltyStatus::Executed);
    }

    #[test]
    fn execute_nonexistent_rule() {
        let mut e = PenaltyEngine::new();
        assert!(e.execute_penalty(999, PartyId(1), 0).is_none());
    }

    #[test]
    fn max_applications_limit() {
        let mut e = PenaltyEngine::new();
        let mut rule = make_rule(1, PenaltyKind::Warning, 0);
        rule.max_applications = 2;
        e.add_rule(rule);

        assert!(e.execute_penalty(1, PartyId(1), 1).is_some());
        assert!(e.execute_penalty(1, PartyId(1), 2).is_some());
        assert!(e.execute_penalty(1, PartyId(1), 3).is_none()); // 上限
    }

    #[test]
    fn waive_penalty() {
        let mut e = PenaltyEngine::new();
        e.add_rule(make_rule(1, PenaltyKind::FixedAmount, 1000));
        let idx = e.execute_penalty(1, PartyId(1), 0).unwrap();
        assert!(e.waive_penalty(idx));
        assert_eq!(e.get_record(idx).unwrap().status, PenaltyStatus::Waived);
    }

    #[test]
    fn dispute_penalty() {
        let mut e = PenaltyEngine::new();
        e.add_rule(make_rule(1, PenaltyKind::FixedAmount, 1000));
        let idx = e.execute_penalty(1, PartyId(1), 0).unwrap();
        assert!(e.dispute_penalty(idx));
        assert_eq!(e.get_record(idx).unwrap().status, PenaltyStatus::Disputed);
    }

    #[test]
    fn waive_out_of_bounds() {
        let mut e = PenaltyEngine::new();
        assert!(!e.waive_penalty(0));
    }

    #[test]
    fn total_penalty_for_party() {
        let mut e = PenaltyEngine::new();
        e.add_rule(make_rule(1, PenaltyKind::FixedAmount, 1000));
        e.add_rule(make_rule(2, PenaltyKind::DailyLateFee, 500));
        e.execute_penalty(1, PartyId(10), 0);
        e.execute_penalty(2, PartyId(10), 1);
        e.execute_penalty(1, PartyId(20), 2);
        assert_eq!(e.total_penalty_for(PartyId(10)), 1500);
        assert_eq!(e.total_penalty_for(PartyId(20)), 1000);
    }

    #[test]
    fn waived_not_counted_in_total() {
        let mut e = PenaltyEngine::new();
        e.add_rule(make_rule(1, PenaltyKind::FixedAmount, 1000));
        let idx = e.execute_penalty(1, PartyId(1), 0).unwrap();
        e.waive_penalty(idx);
        assert_eq!(e.total_penalty_for(PartyId(1)), 0);
    }

    #[test]
    fn record_hash_nonzero() {
        let mut e = PenaltyEngine::new();
        e.add_rule(make_rule(1, PenaltyKind::FixedAmount, 1000));
        let idx = e.execute_penalty(1, PartyId(1), 0).unwrap();
        assert_ne!(e.get_record(idx).unwrap().record_hash, 0);
    }

    #[test]
    fn penalty_kind_eq() {
        assert_eq!(PenaltyKind::FixedAmount, PenaltyKind::FixedAmount);
        assert_ne!(PenaltyKind::FixedAmount, PenaltyKind::Termination);
    }

    #[test]
    fn default_engine() {
        let e = PenaltyEngine::default();
        assert_eq!(e.rule_count(), 0);
    }
}
