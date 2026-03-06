//! Dispute Resolution — チャレンジ/アピール/仲裁メカニズム。
//!
//! 契約紛争のライフサイクル管理。
//! 申立 → 応答 → 仲裁 → 裁定 の標準的なフロー。

use crate::contract::{ContractId, PartyId};
use crate::hash_utils::fnv1a;

/// 紛争状態。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisputeStatus {
    /// 申立済み。
    Filed,
    /// 応答待ち。
    AwaitingResponse,
    /// 仲裁中。
    InArbitration,
    /// 裁定済み。
    Resolved,
    /// 取下げ。
    Withdrawn,
    /// 期限切れ。
    Expired,
}

/// 裁定結果。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Resolution {
    /// 申立人勝訴。
    ClaimantWins,
    /// 被申立人勝訴。
    RespondentWins,
    /// 和解。
    Settlement,
    /// 却下。
    Dismissed,
}

/// 紛争記録。
#[derive(Debug, Clone)]
pub struct Dispute {
    /// 紛争 ID。
    pub id: u64,
    /// 対象契約。
    pub contract_id: ContractId,
    /// 申立人。
    pub claimant: PartyId,
    /// 被申立人。
    pub respondent: PartyId,
    /// 状態。
    pub status: DisputeStatus,
    /// 申立理由ハッシュ。
    pub reason_hash: u64,
    /// 申立時刻。
    pub filed_ns: u64,
    /// 応答期限。
    pub response_deadline_ns: u64,
    /// 裁定結果。
    pub resolution: Option<Resolution>,
    /// 賠償額 (ticks)。
    pub awarded_ticks: i128,
    /// 仲裁人 ID。
    pub arbitrator: Option<u64>,
}

/// 紛争管理。
#[derive(Debug)]
pub struct DisputeManager {
    /// 紛争記録。
    disputes: Vec<Dispute>,
    /// 次の紛争 ID。
    next_id: u64,
    /// デフォルト応答期限 (ナノ秒)。
    pub default_response_window_ns: u64,
}

impl DisputeManager {
    /// 新しい紛争管理を作成。
    #[must_use]
    pub const fn new() -> Self {
        Self {
            disputes: Vec::new(),
            next_id: 1,
            default_response_window_ns: 7 * 24 * 3600 * 1_000_000_000, // 7日
        }
    }

    /// 紛争を申立。
    pub fn file_dispute(
        &mut self,
        contract_id: ContractId,
        claimant: PartyId,
        respondent: PartyId,
        reason: &str,
        now_ns: u64,
    ) -> u64 {
        let id = self.next_id;
        self.next_id += 1;

        self.disputes.push(Dispute {
            id,
            contract_id,
            claimant,
            respondent,
            status: DisputeStatus::Filed,
            reason_hash: fnv1a(reason.as_bytes()),
            filed_ns: now_ns,
            response_deadline_ns: now_ns + self.default_response_window_ns,
            resolution: None,
            awarded_ticks: 0,
            arbitrator: None,
        });

        id
    }

    /// 応答を記録 (状態を仲裁中に遷移)。
    pub fn respond(&mut self, dispute_id: u64) -> bool {
        if let Some(d) = self.disputes.iter_mut().find(|d| d.id == dispute_id) {
            if d.status == DisputeStatus::Filed || d.status == DisputeStatus::AwaitingResponse {
                d.status = DisputeStatus::InArbitration;
                return true;
            }
        }
        false
    }

    /// 仲裁人を割当。
    pub fn assign_arbitrator(&mut self, dispute_id: u64, arbitrator_id: u64) -> bool {
        if let Some(d) = self.disputes.iter_mut().find(|d| d.id == dispute_id) {
            d.arbitrator = Some(arbitrator_id);
            if d.status == DisputeStatus::Filed {
                d.status = DisputeStatus::InArbitration;
            }
            return true;
        }
        false
    }

    /// 裁定を記録。
    pub fn resolve(
        &mut self,
        dispute_id: u64,
        resolution: Resolution,
        awarded_ticks: i128,
    ) -> bool {
        if let Some(d) = self.disputes.iter_mut().find(|d| d.id == dispute_id) {
            if d.status == DisputeStatus::Resolved || d.status == DisputeStatus::Withdrawn {
                return false;
            }
            d.status = DisputeStatus::Resolved;
            d.resolution = Some(resolution);
            d.awarded_ticks = awarded_ticks;
            return true;
        }
        false
    }

    /// 紛争を取下げ。
    pub fn withdraw(&mut self, dispute_id: u64) -> bool {
        if let Some(d) = self.disputes.iter_mut().find(|d| d.id == dispute_id) {
            if d.status != DisputeStatus::Resolved {
                d.status = DisputeStatus::Withdrawn;
                return true;
            }
        }
        false
    }

    /// 期限切れ紛争をマーク。
    pub fn expire_overdue(&mut self, now_ns: u64) -> usize {
        let mut count = 0;
        for d in &mut self.disputes {
            if (d.status == DisputeStatus::Filed || d.status == DisputeStatus::AwaitingResponse)
                && now_ns > d.response_deadline_ns
            {
                d.status = DisputeStatus::Expired;
                count += 1;
            }
        }
        count
    }

    /// 紛争を ID で検索。
    #[must_use]
    pub fn find(&self, dispute_id: u64) -> Option<&Dispute> {
        self.disputes.iter().find(|d| d.id == dispute_id)
    }

    /// 紛争数。
    #[must_use]
    pub const fn count(&self) -> usize {
        self.disputes.len()
    }

    /// 契約の紛争を検索。
    #[must_use]
    pub fn disputes_for_contract(&self, contract_id: ContractId) -> Vec<&Dispute> {
        self.disputes
            .iter()
            .filter(|d| d.contract_id == contract_id)
            .collect()
    }

    /// 当事者の紛争を検索。
    #[must_use]
    pub fn disputes_for_party(&self, party: PartyId) -> Vec<&Dispute> {
        self.disputes
            .iter()
            .filter(|d| d.claimant == party || d.respondent == party)
            .collect()
    }
}

impl Default for DisputeManager {
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

    #[test]
    fn empty_manager() {
        let m = DisputeManager::new();
        assert_eq!(m.count(), 0);
    }

    #[test]
    fn file_dispute() {
        let mut m = DisputeManager::new();
        let id = m.file_dispute(ContractId(1), PartyId(10), PartyId(20), "breach", 1000);
        assert_eq!(m.count(), 1);
        let d = m.find(id).unwrap();
        assert_eq!(d.status, DisputeStatus::Filed);
        assert_eq!(d.claimant, PartyId(10));
    }

    #[test]
    fn respond_moves_to_arbitration() {
        let mut m = DisputeManager::new();
        let id = m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "test", 0);
        assert!(m.respond(id));
        assert_eq!(m.find(id).unwrap().status, DisputeStatus::InArbitration);
    }

    #[test]
    fn assign_arbitrator() {
        let mut m = DisputeManager::new();
        let id = m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "test", 0);
        assert!(m.assign_arbitrator(id, 99));
        let d = m.find(id).unwrap();
        assert_eq!(d.arbitrator, Some(99));
        assert_eq!(d.status, DisputeStatus::InArbitration);
    }

    #[test]
    fn resolve_claimant_wins() {
        let mut m = DisputeManager::new();
        let id = m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "test", 0);
        assert!(m.resolve(id, Resolution::ClaimantWins, 5000));
        let d = m.find(id).unwrap();
        assert_eq!(d.status, DisputeStatus::Resolved);
        assert_eq!(d.resolution, Some(Resolution::ClaimantWins));
        assert_eq!(d.awarded_ticks, 5000);
    }

    #[test]
    fn cannot_resolve_already_resolved() {
        let mut m = DisputeManager::new();
        let id = m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "test", 0);
        m.resolve(id, Resolution::Settlement, 0);
        assert!(!m.resolve(id, Resolution::ClaimantWins, 1000));
    }

    #[test]
    fn withdraw() {
        let mut m = DisputeManager::new();
        let id = m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "test", 0);
        assert!(m.withdraw(id));
        assert_eq!(m.find(id).unwrap().status, DisputeStatus::Withdrawn);
    }

    #[test]
    fn cannot_withdraw_resolved() {
        let mut m = DisputeManager::new();
        let id = m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "test", 0);
        m.resolve(id, Resolution::Dismissed, 0);
        assert!(!m.withdraw(id));
    }

    #[test]
    fn expire_overdue() {
        let mut m = DisputeManager::new();
        m.default_response_window_ns = 1000;
        m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "test", 0);
        let expired = m.expire_overdue(2000);
        assert_eq!(expired, 1);
    }

    #[test]
    fn expire_not_overdue() {
        let mut m = DisputeManager::new();
        m.default_response_window_ns = 10000;
        m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "test", 0);
        let expired = m.expire_overdue(5000);
        assert_eq!(expired, 0);
    }

    #[test]
    fn disputes_for_contract() {
        let mut m = DisputeManager::new();
        m.file_dispute(ContractId(1), PartyId(1), PartyId(2), "a", 0);
        m.file_dispute(ContractId(2), PartyId(1), PartyId(3), "b", 0);
        m.file_dispute(ContractId(1), PartyId(3), PartyId(2), "c", 0);
        assert_eq!(m.disputes_for_contract(ContractId(1)).len(), 2);
    }

    #[test]
    fn disputes_for_party() {
        let mut m = DisputeManager::new();
        m.file_dispute(ContractId(1), PartyId(10), PartyId(20), "a", 0);
        m.file_dispute(ContractId(2), PartyId(30), PartyId(10), "b", 0);
        assert_eq!(m.disputes_for_party(PartyId(10)).len(), 2);
    }

    #[test]
    fn dispute_status_eq() {
        assert_eq!(DisputeStatus::Filed, DisputeStatus::Filed);
        assert_ne!(DisputeStatus::Filed, DisputeStatus::Resolved);
    }

    #[test]
    fn resolution_eq() {
        assert_eq!(Resolution::Settlement, Resolution::Settlement);
        assert_ne!(Resolution::Settlement, Resolution::Dismissed);
    }

    #[test]
    fn default_manager() {
        let m = DisputeManager::default();
        assert_eq!(m.count(), 0);
    }
}
