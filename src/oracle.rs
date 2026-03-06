//! Oracle Integration — 条件評価オラクル。
//!
//! 契約条件の外部データソース抽象化。
//! オラクル判定結果をハッシュで検証し、改竄を防止。

use crate::contract::ContractId;
use crate::hash_utils::fnv1a;

/// オラクル種別。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleType {
    /// 価格フィード。
    PriceFeed,
    /// 時間条件 (期限到達)。
    TimeCondition,
    /// 外部イベント (配送完了、検収等)。
    ExternalEvent,
    /// 多数決 (マルチシグ的)。
    Consensus,
    /// カスタム。
    Custom,
}

/// オラクル判定結果。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleVerdict {
    /// 条件充足。
    Satisfied,
    /// 条件未充足。
    NotSatisfied,
    /// 判定不能 (データ不足)。
    Inconclusive,
    /// タイムアウト。
    TimedOut,
}

/// オラクル応答。
#[derive(Debug, Clone)]
pub struct OracleResponse {
    /// オラクル ID。
    pub oracle_id: u64,
    /// 判定結果。
    pub verdict: OracleVerdict,
    /// 判定時刻 (Unix ns)。
    pub timestamp_ns: u64,
    /// 応答データのハッシュ (検証用)。
    pub data_hash: u64,
    /// 対象契約 ID。
    pub contract_id: ContractId,
    /// 対象条件インデックス。
    pub condition_index: usize,
}

/// オラクル登録情報。
#[derive(Debug, Clone)]
pub struct OracleRegistration {
    /// オラクル ID。
    pub id: u64,
    /// オラクル種別。
    pub oracle_type: OracleType,
    /// 名称ハッシュ。
    pub name_hash: u64,
    /// 信頼スコア (0-100)。
    pub trust_score: u8,
    /// 有効フラグ。
    pub active: bool,
}

/// オラクルレジストリ。
#[derive(Debug)]
pub struct OracleRegistry {
    /// 登録済みオラクル。
    oracles: Vec<OracleRegistration>,
    /// 応答履歴。
    responses: Vec<OracleResponse>,
}

impl OracleRegistry {
    /// 空のレジストリを作成。
    #[must_use]
    pub const fn new() -> Self {
        Self {
            oracles: Vec::new(),
            responses: Vec::new(),
        }
    }

    /// オラクルを登録。
    pub fn register(&mut self, oracle_type: OracleType, name: &str, trust_score: u8) -> u64 {
        let id = fnv1a(name.as_bytes());
        self.oracles.push(OracleRegistration {
            id,
            oracle_type,
            name_hash: fnv1a(name.as_bytes()),
            trust_score: trust_score.min(100),
            active: true,
        });
        id
    }

    /// オラクル応答を記録。
    pub fn submit_response(&mut self, response: OracleResponse) {
        self.responses.push(response);
    }

    /// オラクルを ID で検索。
    #[must_use]
    pub fn find_oracle(&self, id: u64) -> Option<&OracleRegistration> {
        self.oracles.iter().find(|o| o.id == id)
    }

    /// オラクルを無効化。
    pub fn deactivate(&mut self, id: u64) {
        if let Some(o) = self.oracles.iter_mut().find(|o| o.id == id) {
            o.active = false;
        }
    }

    /// 登録数。
    #[must_use]
    pub const fn oracle_count(&self) -> usize {
        self.oracles.len()
    }

    /// 応答数。
    #[must_use]
    pub const fn response_count(&self) -> usize {
        self.responses.len()
    }

    /// 契約の条件に対する最新応答を取得。
    #[must_use]
    pub fn latest_response(
        &self,
        contract_id: ContractId,
        condition_index: usize,
    ) -> Option<&OracleResponse> {
        self.responses
            .iter()
            .rev()
            .find(|r| r.contract_id == contract_id && r.condition_index == condition_index)
    }

    /// 応答データのハッシュ検証。
    #[must_use]
    pub fn verify_response(response: &OracleResponse, raw_data: &[u8]) -> bool {
        fnv1a(raw_data) == response.data_hash
    }
}

impl Default for OracleRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// 応答データからハッシュを生成。
#[must_use]
pub fn compute_data_hash(data: &[u8]) -> u64 {
    fnv1a(data)
}

/// マルチオラクル合意チェック。
///
/// `threshold` 個以上の Satisfied 判定で合意。
#[must_use]
pub fn check_consensus(responses: &[OracleResponse], threshold: usize) -> OracleVerdict {
    let satisfied = responses
        .iter()
        .filter(|r| r.verdict == OracleVerdict::Satisfied)
        .count();
    if satisfied >= threshold {
        OracleVerdict::Satisfied
    } else {
        OracleVerdict::NotSatisfied
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_registry() {
        let r = OracleRegistry::new();
        assert_eq!(r.oracle_count(), 0);
        assert_eq!(r.response_count(), 0);
    }

    #[test]
    fn register_oracle() {
        let mut r = OracleRegistry::new();
        let id = r.register(OracleType::PriceFeed, "BTC/USD", 90);
        assert_eq!(r.oracle_count(), 1);
        let o = r.find_oracle(id).unwrap();
        assert_eq!(o.oracle_type, OracleType::PriceFeed);
        assert!(o.active);
    }

    #[test]
    fn deactivate_oracle() {
        let mut r = OracleRegistry::new();
        let id = r.register(OracleType::TimeCondition, "deadline", 80);
        r.deactivate(id);
        let o = r.find_oracle(id).unwrap();
        assert!(!o.active);
    }

    #[test]
    fn submit_and_find_response() {
        let mut r = OracleRegistry::new();
        r.submit_response(OracleResponse {
            oracle_id: 1,
            verdict: OracleVerdict::Satisfied,
            timestamp_ns: 1000,
            data_hash: fnv1a(b"test"),
            contract_id: ContractId(42),
            condition_index: 0,
        });
        let resp = r.latest_response(ContractId(42), 0).unwrap();
        assert_eq!(resp.verdict, OracleVerdict::Satisfied);
    }

    #[test]
    fn latest_response_returns_newest() {
        let mut r = OracleRegistry::new();
        r.submit_response(OracleResponse {
            oracle_id: 1,
            verdict: OracleVerdict::NotSatisfied,
            timestamp_ns: 1000,
            data_hash: 0,
            contract_id: ContractId(1),
            condition_index: 0,
        });
        r.submit_response(OracleResponse {
            oracle_id: 1,
            verdict: OracleVerdict::Satisfied,
            timestamp_ns: 2000,
            data_hash: 0,
            contract_id: ContractId(1),
            condition_index: 0,
        });
        let resp = r.latest_response(ContractId(1), 0).unwrap();
        assert_eq!(resp.verdict, OracleVerdict::Satisfied);
    }

    #[test]
    fn verify_response_valid() {
        let data = b"price=50000";
        let resp = OracleResponse {
            oracle_id: 1,
            verdict: OracleVerdict::Satisfied,
            timestamp_ns: 0,
            data_hash: fnv1a(data),
            contract_id: ContractId(1),
            condition_index: 0,
        };
        assert!(OracleRegistry::verify_response(&resp, data));
    }

    #[test]
    fn verify_response_tampered() {
        let resp = OracleResponse {
            oracle_id: 1,
            verdict: OracleVerdict::Satisfied,
            timestamp_ns: 0,
            data_hash: fnv1a(b"original"),
            contract_id: ContractId(1),
            condition_index: 0,
        };
        assert!(!OracleRegistry::verify_response(&resp, b"tampered"));
    }

    #[test]
    fn consensus_satisfied() {
        let responses = vec![
            OracleResponse {
                oracle_id: 1,
                verdict: OracleVerdict::Satisfied,
                timestamp_ns: 0,
                data_hash: 0,
                contract_id: ContractId(1),
                condition_index: 0,
            },
            OracleResponse {
                oracle_id: 2,
                verdict: OracleVerdict::Satisfied,
                timestamp_ns: 0,
                data_hash: 0,
                contract_id: ContractId(1),
                condition_index: 0,
            },
            OracleResponse {
                oracle_id: 3,
                verdict: OracleVerdict::NotSatisfied,
                timestamp_ns: 0,
                data_hash: 0,
                contract_id: ContractId(1),
                condition_index: 0,
            },
        ];
        assert_eq!(check_consensus(&responses, 2), OracleVerdict::Satisfied);
    }

    #[test]
    fn consensus_not_satisfied() {
        let responses = vec![
            OracleResponse {
                oracle_id: 1,
                verdict: OracleVerdict::Satisfied,
                timestamp_ns: 0,
                data_hash: 0,
                contract_id: ContractId(1),
                condition_index: 0,
            },
            OracleResponse {
                oracle_id: 2,
                verdict: OracleVerdict::NotSatisfied,
                timestamp_ns: 0,
                data_hash: 0,
                contract_id: ContractId(1),
                condition_index: 0,
            },
        ];
        assert_eq!(check_consensus(&responses, 2), OracleVerdict::NotSatisfied);
    }

    #[test]
    fn compute_hash() {
        let h = compute_data_hash(b"hello");
        assert_ne!(h, 0);
    }

    #[test]
    fn oracle_type_eq() {
        assert_eq!(OracleType::PriceFeed, OracleType::PriceFeed);
        assert_ne!(OracleType::PriceFeed, OracleType::Consensus);
    }

    #[test]
    fn verdict_eq() {
        assert_eq!(OracleVerdict::Satisfied, OracleVerdict::Satisfied);
        assert_ne!(OracleVerdict::Satisfied, OracleVerdict::TimedOut);
    }

    #[test]
    fn default_registry() {
        let r = OracleRegistry::default();
        assert_eq!(r.oracle_count(), 0);
    }

    #[test]
    fn trust_score_capped() {
        let mut r = OracleRegistry::new();
        let id = r.register(OracleType::Custom, "over", 150);
        let o = r.find_oracle(id).unwrap();
        assert_eq!(o.trust_score, 100);
    }
}
