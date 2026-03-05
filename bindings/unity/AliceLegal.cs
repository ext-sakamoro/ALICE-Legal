// ALICE-Legal — Unity C# Bindings
// License: MIT
// Author: Moroya Sakamoto
//
// 21 DllImport + 4 IDisposable RAII wrappers

using System;
using System.Runtime.InteropServices;
using System.Text;

namespace Alice.Legal
{
    internal static class Native
    {
#if UNITY_IOS && !UNITY_EDITOR
        private const string Lib = "__Internal";
#else
        private const string Lib = "alice_legal";
#endif

        // StatuteTree (5)
        [DllImport(Lib)] public static extern IntPtr alice_statute_new(
            ulong id, byte[] title, uint titleLen);
        [DllImport(Lib)] public static extern ulong alice_statute_add_clause(
            IntPtr tree, byte kind, byte[] content, uint contentLen,
            ulong parentId, ulong effectiveFromNs);
        [DllImport(Lib)] public static extern uint alice_statute_obligations_count(IntPtr tree);
        [DllImport(Lib)] public static extern byte alice_statute_is_effective(
            IntPtr tree, ulong clauseId, ulong atNs);
        [DllImport(Lib)] public static extern void alice_statute_destroy(IntPtr tree);

        // Contract (7)
        [DllImport(Lib)] public static extern IntPtr alice_contract_new(
            ulong id, ulong[] parties, uint partiesLen, ulong createdNs);
        [DllImport(Lib)] public static extern uint alice_contract_add_obligation(
            IntPtr contract, ulong debtor, ulong creditor, long amountTicks, ulong dueNs);
        [DllImport(Lib)] public static extern byte alice_contract_fulfill_obligation(
            IntPtr contract, uint idx);
        [DllImport(Lib)] public static extern byte alice_contract_check_status(
            IntPtr contract, ulong nowNs);
        [DllImport(Lib)] public static extern uint alice_contract_unfulfilled_count(IntPtr contract);
        [DllImport(Lib)] public static extern long alice_contract_total_obligation_i64(IntPtr contract);
        [DllImport(Lib)] public static extern void alice_contract_destroy(IntPtr contract);

        // Procedure (5)
        [DllImport(Lib)] public static extern IntPtr alice_procedure_new(ulong id);
        [DllImport(Lib)] public static extern void alice_procedure_add_step(
            IntPtr proc, byte kind,
            byte[] actor, uint actorLen,
            byte[] content, uint contentLen,
            ulong timestampNs);
        [DllImport(Lib)] public static extern byte alice_procedure_verify_chain(IntPtr proc);
        [DllImport(Lib)] public static extern uint alice_procedure_step_count(IntPtr proc);
        [DllImport(Lib)] public static extern void alice_procedure_destroy(IntPtr proc);

        // AuditLog (4)
        [DllImport(Lib)] public static extern IntPtr alice_audit_new();
        [DllImport(Lib)] public static extern ulong alice_audit_append(
            IntPtr log, byte kind, ulong entityId,
            byte[] actor, uint actorLen,
            byte[] content, uint contentLen,
            ulong timestampNs);
        [DllImport(Lib)] public static extern uint alice_audit_len(IntPtr log);
        [DllImport(Lib)] public static extern void alice_audit_destroy(IntPtr log);
    }

    public sealed class AliceStatuteTree : IDisposable
    {
        private IntPtr _ptr;

        public AliceStatuteTree(ulong id, string title)
        {
            var bytes = Encoding.UTF8.GetBytes(title);
            _ptr = Native.alice_statute_new(id, bytes, (uint)bytes.Length);
        }

        public ulong AddClause(byte kind, string content, ulong parentId, ulong effectiveFromNs)
        {
            var bytes = Encoding.UTF8.GetBytes(content);
            return Native.alice_statute_add_clause(
                _ptr, kind, bytes, (uint)bytes.Length, parentId, effectiveFromNs);
        }

        public uint ObligationsCount => Native.alice_statute_obligations_count(_ptr);

        public bool IsEffective(ulong clauseId, ulong atNs)
            => Native.alice_statute_is_effective(_ptr, clauseId, atNs) != 0;

        public void Dispose()
        {
            if (_ptr != IntPtr.Zero) { Native.alice_statute_destroy(_ptr); _ptr = IntPtr.Zero; }
        }
        ~AliceStatuteTree() => Dispose();
    }

    public sealed class AliceContract : IDisposable
    {
        private IntPtr _ptr;

        public AliceContract(ulong id, ulong[] parties, ulong createdNs)
        {
            _ptr = Native.alice_contract_new(id, parties, (uint)parties.Length, createdNs);
        }

        public uint AddObligation(ulong debtor, ulong creditor, long amountTicks, ulong dueNs)
            => Native.alice_contract_add_obligation(_ptr, debtor, creditor, amountTicks, dueNs);

        public bool FulfillObligation(uint idx)
            => Native.alice_contract_fulfill_obligation(_ptr, idx) != 0;

        public byte CheckStatus(ulong nowNs)
            => Native.alice_contract_check_status(_ptr, nowNs);

        public uint UnfulfilledCount => Native.alice_contract_unfulfilled_count(_ptr);
        public long TotalObligationI64 => Native.alice_contract_total_obligation_i64(_ptr);

        public void Dispose()
        {
            if (_ptr != IntPtr.Zero) { Native.alice_contract_destroy(_ptr); _ptr = IntPtr.Zero; }
        }
        ~AliceContract() => Dispose();
    }

    public sealed class AliceProcedure : IDisposable
    {
        private IntPtr _ptr;

        public AliceProcedure(ulong id)
        {
            _ptr = Native.alice_procedure_new(id);
        }

        public void AddStep(byte kind, string actor, string content, ulong timestampNs)
        {
            var actorBytes = Encoding.UTF8.GetBytes(actor);
            var contentBytes = Encoding.UTF8.GetBytes(content);
            Native.alice_procedure_add_step(
                _ptr, kind,
                actorBytes, (uint)actorBytes.Length,
                contentBytes, (uint)contentBytes.Length,
                timestampNs);
        }

        public bool VerifyChain => Native.alice_procedure_verify_chain(_ptr) != 0;
        public uint StepCount => Native.alice_procedure_step_count(_ptr);

        public void Dispose()
        {
            if (_ptr != IntPtr.Zero) { Native.alice_procedure_destroy(_ptr); _ptr = IntPtr.Zero; }
        }
        ~AliceProcedure() => Dispose();
    }

    public sealed class AliceAuditLog : IDisposable
    {
        private IntPtr _ptr;

        public AliceAuditLog()
        {
            _ptr = Native.alice_audit_new();
        }

        public ulong Append(byte kind, ulong entityId, string actor, string content, ulong timestampNs)
        {
            var actorBytes = Encoding.UTF8.GetBytes(actor);
            var contentBytes = Encoding.UTF8.GetBytes(content);
            return Native.alice_audit_append(
                _ptr, kind, entityId,
                actorBytes, (uint)actorBytes.Length,
                contentBytes, (uint)contentBytes.Length,
                timestampNs);
        }

        public uint Len => Native.alice_audit_len(_ptr);

        public void Dispose()
        {
            if (_ptr != IntPtr.Zero) { Native.alice_audit_destroy(_ptr); _ptr = IntPtr.Zero; }
        }
        ~AliceAuditLog() => Dispose();
    }
}
