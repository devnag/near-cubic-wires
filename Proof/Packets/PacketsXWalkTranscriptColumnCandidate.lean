import Proof.Packets.PacketsXWalkTranscriptColumnResetMajority
import Proof.Packets.PacketsXMajorityCompleteBootstrapReset

/-! A closed physical candidate transaction: evaluate the ordered majority,
append its exact packet, restore the majority arena, clear the column bank,
and increment the resident candidate counter. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumnArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Completion.SourceDock Theorem25Completion.CycleBounds
noncomputable section

def candidate := Composition.machine consume finish
def candidateBudget (C w T index : Nat) := consumeBudget C w T+1+
  finishBudget (commonReserve C w) ((commonReserve C w)^2) T index

theorem candidate_run (palette : Fin 10→List Bool) (C w N T S index : Nat) (support : Finset Nat) (d : Nat)
    (source target result : List Bool) (old : PacketVector.Packet) (ps : List (Ring.Poly Nat))
    (hS : ∀j∈support,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded support d P)
    (hfit : (support.card+1)^(d*ps.length)≤2^w) (hAtom : (support.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hCodes : 2^ps.length≤2^w) (hw : 1≤w) (hlen : ps.length=T)
    (hc : MajorityComplete.Bootstrap.Compatible palette C (commonReserve C w) T ((commonReserve C w)^2))
    (H : Fin 471→Nat) (A : Fin 471→List Bool) (hh : ReadyHeads H result.length)
    (ha : Ready palette C (commonReserve C w) ((commonReserve C w)^2) N T S index
      source old target result ps A)
    (ht : target=OrderedPacketStep.bank C (commonReserve C w) ps) :
    let R:=commonReserve C w
    let packet:=(MajorityComplete.majority ps).map (maskNat C)
    let next:=result++PacketVector.entry R packet
    ∃B,Step candidate (candidateBudget C w T index) H A (Function.update H 29 next.length) B ∧
      Ready palette C R (R^2) N T S (index+1) source old (List.replicate (T*(2*R)) false) next ps B ∧
      ReadyHeads (Function.update H 29 next.length) next.length := by
  dsimp only
  have hc' : MajorityComplete.Bootstrap.Compatible palette C (commonReserve C w) ps.length
      ((commonReserve C w)^2) := by simpa only [hlen] using hc
  have htlen : target.length=T*(2*commonReserve C w) := by
    rw [ht,MajorityComplete.bank_length C w ps
      (fun P hp=>(NormalizedIntermediate.census (hps P hp)).trans hAtom),hlen]
  obtain ⟨middle,first,hm,hmh⟩:=consume_run palette C w N T S index support d source target result old ps
    hS hps hfit hAtom hN hCodes hw H A hh ha ht
  obtain ⟨out,last,ho⟩:=finish_run palette C (commonReserve C w) ((commonReserve C w)^2) N T S index
    source target _ old ps (MajorityComplete.palette_fits C w ps.length hN hCodes hw) hc'
    (MajorityComplete.Bootstrap.final_work_length C w support d ps hS hps hfit hAtom hN hCodes hw)
    _ middle hmh hm htlen
  refine ⟨out,?_,ho,hmh⟩
  simpa only [candidate,candidateBudget,hlen] using first.seq last

def worker := Composition.machine extract candidate
def workerBudget (C w N T index : Nat) := TranscriptColumn.budget (commonReserve C w) N T index+1+
  candidateBudget C w T index

theorem worker_run (palette : Fin 10→List Bool) (C w N T S : Nat) (support : Finset Nat) (d : Nat)
    (rows : Nat→List PacketVector.Packet) (rowLength : ∀i,(rows i).length=N) (column : Fin N)
    (old : PacketVector.Packet) (rowFits : ∀i,∀P∈rows i,PacketVector.Fits (commonReserve C w) P)
    (oldFits : PacketVector.Fits (commonReserve C w) old) (result : List Bool) (ps : List (Ring.Poly Nat))
    (hS : ∀j∈support,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded support d P)
    (hfit : (support.card+1)^(d*ps.length)≤2^w) (hAtom : (support.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hCodes : 2^ps.length≤2^w) (hw : 1≤w) (hlen : ps.length=T)
    (hc : MajorityComplete.Bootstrap.Compatible palette C (commonReserve C w) T ((commonReserve C w)^2))
    (hp : List.ofFn (fun i : Fin T=>TranscriptColumn.rowPacket N rows rowLength column i.val)=
      ps.map (fun P=>P.map (maskNat C)))
    (H : Fin 471→Nat) (A : Fin 471→List Bool) (hh : ReadyHeads H result.length)
    (ha : Ready palette C (commonReserve C w) ((commonReserve C w)^2) N T S column.val
      (PacketTranscript.prefixBank (commonReserve C w) rows T) old
      (List.replicate (T*(2*commonReserve C w)) false) result ps A) :
    let R:=commonReserve C w
    let packet:=(MajorityComplete.majority ps).map (maskNat C)
    let next:=result++PacketVector.entry R packet
    ∃B,Step worker (workerBudget C w N T column.val) H A (Function.update H 29 next.length) B ∧
      Ready palette C R (R^2) N T S (column.val+1) (PacketTranscript.prefixBank R rows T)
        (TranscriptColumn.previous (TranscriptColumn.rowPacket N rows rowLength column) old T)
        (List.replicate (T*(2*R)) false) next ps B ∧
      ReadyHeads (Function.update H 29 next.length) next.length := by
  dsimp only
  obtain ⟨middle,first,hm⟩:=extract_ready palette C (commonReserve C w) ((commonReserve C w)^2) N T S
    rows rowLength column old rowFits oldFits ps result H A hh ha
  obtain ⟨out,last,ho,hhout⟩:=candidate_run palette C w N T S column.val support d
    _ _ result _ ps hS hps hfit hAtom hN hCodes hw hlen hc H middle hh hm
    (by rw [hp];rfl)
  refine ⟨out,?_,ho,hhout⟩
  exact first.seq last

end
end Theorem25Completion.WalkTranscriptColumnArena
