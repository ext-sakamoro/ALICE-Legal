// ALICE-Legal — UE5 C++ Bindings
// License: MIT
// Author: Moroya Sakamoto
//
// 21 extern "C" declarations + 4 RAII wrapper classes

#pragma once

#include <cstdint>
#include <utility>

// ── extern "C" declarations ─────────────────────────────────────────

extern "C" {

// StatuteTree (5)
void*    alice_statute_new(uint64_t id, const uint8_t* title, uint32_t title_len);
uint64_t alice_statute_add_clause(void* tree, uint8_t kind, const uint8_t* content,
             uint32_t content_len, uint64_t parent_id, uint64_t effective_from_ns);
uint32_t alice_statute_obligations_count(const void* tree);
uint8_t  alice_statute_is_effective(const void* tree, uint64_t clause_id, uint64_t at_ns);
void     alice_statute_destroy(void* tree);

// Contract (7)
void*    alice_contract_new(uint64_t id, const uint64_t* parties, uint32_t parties_len,
             uint64_t created_ns);
uint32_t alice_contract_add_obligation(void* contract, uint64_t debtor, uint64_t creditor,
             int64_t amount_ticks, uint64_t due_ns);
uint8_t  alice_contract_fulfill_obligation(void* contract, uint32_t idx);
uint8_t  alice_contract_check_status(void* contract, uint64_t now_ns);
uint32_t alice_contract_unfulfilled_count(const void* contract);
int64_t  alice_contract_total_obligation_i64(const void* contract);
void     alice_contract_destroy(void* contract);

// Procedure (5)
void*    alice_procedure_new(uint64_t id);
void     alice_procedure_add_step(void* proc, uint8_t kind,
             const uint8_t* actor, uint32_t actor_len,
             const uint8_t* content, uint32_t content_len, uint64_t timestamp_ns);
uint8_t  alice_procedure_verify_chain(const void* proc);
uint32_t alice_procedure_step_count(const void* proc);
void     alice_procedure_destroy(void* proc);

// AuditLog (4)
void*    alice_audit_new();
uint64_t alice_audit_append(void* log, uint8_t kind, uint64_t entity_id,
             const uint8_t* actor, uint32_t actor_len,
             const uint8_t* content, uint32_t content_len, uint64_t timestamp_ns);
uint32_t alice_audit_len(const void* log);
void     alice_audit_destroy(void* log);

} // extern "C"

// ── RAII wrappers ───────────────────────────────────────────────────

class AliceStatuteTree {
    void* ptr_;
public:
    AliceStatuteTree(uint64_t id, const uint8_t* title, uint32_t title_len)
        : ptr_(alice_statute_new(id, title, title_len)) {}

    ~AliceStatuteTree() { if (ptr_) alice_statute_destroy(ptr_); }

    AliceStatuteTree(const AliceStatuteTree&) = delete;
    AliceStatuteTree& operator=(const AliceStatuteTree&) = delete;
    AliceStatuteTree(AliceStatuteTree&& o) noexcept : ptr_(std::exchange(o.ptr_, nullptr)) {}
    AliceStatuteTree& operator=(AliceStatuteTree&& o) noexcept {
        if (this != &o) { if (ptr_) alice_statute_destroy(ptr_); ptr_ = std::exchange(o.ptr_, nullptr); }
        return *this;
    }

    uint64_t AddClause(uint8_t kind, const uint8_t* content, uint32_t content_len,
                       uint64_t parent_id, uint64_t effective_from_ns) const {
        return alice_statute_add_clause(ptr_, kind, content, content_len, parent_id, effective_from_ns);
    }

    uint32_t ObligationsCount() const { return alice_statute_obligations_count(ptr_); }
    bool IsEffective(uint64_t clause_id, uint64_t at_ns) const {
        return alice_statute_is_effective(ptr_, clause_id, at_ns) != 0;
    }
};

class AliceContract {
    void* ptr_;
public:
    AliceContract(uint64_t id, const uint64_t* parties, uint32_t parties_len, uint64_t created_ns)
        : ptr_(alice_contract_new(id, parties, parties_len, created_ns)) {}

    ~AliceContract() { if (ptr_) alice_contract_destroy(ptr_); }

    AliceContract(const AliceContract&) = delete;
    AliceContract& operator=(const AliceContract&) = delete;
    AliceContract(AliceContract&& o) noexcept : ptr_(std::exchange(o.ptr_, nullptr)) {}
    AliceContract& operator=(AliceContract&& o) noexcept {
        if (this != &o) { if (ptr_) alice_contract_destroy(ptr_); ptr_ = std::exchange(o.ptr_, nullptr); }
        return *this;
    }

    uint32_t AddObligation(uint64_t debtor, uint64_t creditor, int64_t amount_ticks, uint64_t due_ns) {
        return alice_contract_add_obligation(ptr_, debtor, creditor, amount_ticks, due_ns);
    }

    bool FulfillObligation(uint32_t idx) {
        return alice_contract_fulfill_obligation(ptr_, idx) != 0;
    }

    uint8_t CheckStatus(uint64_t now_ns) {
        return alice_contract_check_status(ptr_, now_ns);
    }

    uint32_t UnfulfilledCount() const { return alice_contract_unfulfilled_count(ptr_); }
    int64_t TotalObligationI64() const { return alice_contract_total_obligation_i64(ptr_); }
};

class AliceProcedure {
    void* ptr_;
public:
    explicit AliceProcedure(uint64_t id) : ptr_(alice_procedure_new(id)) {}

    ~AliceProcedure() { if (ptr_) alice_procedure_destroy(ptr_); }

    AliceProcedure(const AliceProcedure&) = delete;
    AliceProcedure& operator=(const AliceProcedure&) = delete;
    AliceProcedure(AliceProcedure&& o) noexcept : ptr_(std::exchange(o.ptr_, nullptr)) {}
    AliceProcedure& operator=(AliceProcedure&& o) noexcept {
        if (this != &o) { if (ptr_) alice_procedure_destroy(ptr_); ptr_ = std::exchange(o.ptr_, nullptr); }
        return *this;
    }

    void AddStep(uint8_t kind, const uint8_t* actor, uint32_t actor_len,
                 const uint8_t* content, uint32_t content_len, uint64_t timestamp_ns) {
        alice_procedure_add_step(ptr_, kind, actor, actor_len, content, content_len, timestamp_ns);
    }

    bool VerifyChain() const { return alice_procedure_verify_chain(ptr_) != 0; }
    uint32_t StepCount() const { return alice_procedure_step_count(ptr_); }
};

class AliceAuditLog {
    void* ptr_;
public:
    AliceAuditLog() : ptr_(alice_audit_new()) {}

    ~AliceAuditLog() { if (ptr_) alice_audit_destroy(ptr_); }

    AliceAuditLog(const AliceAuditLog&) = delete;
    AliceAuditLog& operator=(const AliceAuditLog&) = delete;
    AliceAuditLog(AliceAuditLog&& o) noexcept : ptr_(std::exchange(o.ptr_, nullptr)) {}
    AliceAuditLog& operator=(AliceAuditLog&& o) noexcept {
        if (this != &o) { if (ptr_) alice_audit_destroy(ptr_); ptr_ = std::exchange(o.ptr_, nullptr); }
        return *this;
    }

    uint64_t Append(uint8_t kind, uint64_t entity_id,
                    const uint8_t* actor, uint32_t actor_len,
                    const uint8_t* content, uint32_t content_len, uint64_t timestamp_ns) {
        return alice_audit_append(ptr_, kind, entity_id, actor, actor_len,
                                  content, content_len, timestamp_ns);
    }

    uint32_t Len() const { return alice_audit_len(ptr_); }
};
