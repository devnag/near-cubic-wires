import Proof.Packets.PacketsXWalkTranscriptColumnAllFirst

/-! One genuinely executed remaining-candidate iteration with an exact
ordered output prefix and the previous candidate's physical operand packet. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds WalkTranscriptColumnArena
noncomputable section
variable {population active depth n : Nat}

def AllReady (palette : Fin 10→List Bool) (C R S : Nat) (mask : Finset (Fin population))
    (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (i : Nat) (A : Fin 471→List Bool) :=
  Ready palette C R (R^2) (population+1) (n+1) S (i+1)
    (PacketTranscript.prefixBank R (WalkLiteralLoop.rows C mask wins sample) (n+1))
    (allLast C mask wins sample i) (List.replicate ((n+1)*(2*R)) false)
    (allResult C R mask wins sample (i+1)) (allPolys mask wins sample (i+1)) A

theorem workerBudget_mono (C w N T i j : Nat) (h : i≤j) :
    workerBudget C w N T i≤workerBudget C w N T j := by
  unfold workerBudget candidateBudget finishBudget TranscriptColumn.budget TranscriptColumn.resetBudget
  gcongr

theorem all_next_run (palette : Fin 10→List Bool) (C w d root S L : Nat)
    (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (hfit : (population+1)^(d*(n+1))≤2^w) (hVisits : n+1≤2^w) (hCodes : 2^(n+1)≤2^w)
    (hc : MajorityComplete.Bootstrap.Compatible palette C (commonReserve C w) (n+1) ((commonReserve C w)^2))
    (H : Fin 471→Nat) (i : Nat) (hi : i<population) (A : Fin 471→List Bool)
    (hh : ReadyHeads (allHeads H C (commonReserve C w) mask wins sample i)
      (allResult C (commonReserve C w) mask wins sample (i+1)).length)
    (ha : AllReady palette C (commonReserve C w) S mask wins sample i A) :
    ∃B,Step worker (workerBudget C w (population+1) (n+1) population)
        (allHeads H C (commonReserve C w) mask wins sample i) A
        (allHeads H C (commonReserve C w) mask wins sample (i+1)) B ∧
      AllReady palette C (commonReserve C w) S mask wins sample (i+1) B ∧
      ReadyHeads (allHeads H C (commonReserve C w) mask wins sample (i+1))
        (allResult C (commonReserve C w) mask wins sample ((i+1)+1)).length := by
  have hv := allColumn_val population (i+1) (by omega)
  have hw : 1≤w := by have hh:=h.width;omega
  have hpf:=MajorityComplete.palette_fits C w (n+1) hVisits hCodes hw
  obtain ⟨B,actual,ready,heads⟩:=walk_worker_run palette C w d root S L mask wins h sample
    (allColumn population (i+1)) (allLast C mask wins sample i)
    (allLast_fits C w d root S L mask wins h sample i)
    (allResult C (commonReserve C w) mask wins sample (i+1)) hfit hVisits hCodes hc _ A hh
    (by simpa only [AllReady,allPolys,hv] using ha)
  change Step worker (workerBudget C w (population+1) (n+1) (allColumn population (i+1)).val)
    (allHeads H C (commonReserve C w) mask wins sample i) A
    (Function.update (allHeads H C (commonReserve C w) mask wins sample i) 29
      (allResult C (commonReserve C w) mask wins sample (i+1)++
        PacketVector.entry (commonReserve C w) (allPacket C mask wins sample (i+1))).length) B at actual
  change Ready palette C (commonReserve C w) ((commonReserve C w)^2) (population+1) (n+1) S
    ((allColumn population (i+1)).val+1)
    (PacketTranscript.prefixBank (commonReserve C w) (WalkLiteralLoop.rows C mask wins sample) (n+1))
    (allLast C mask wins sample (i+1)) (List.replicate ((n+1)*(2*commonReserve C w)) false)
    (allResult C (commonReserve C w) mask wins sample (i+1)++
      PacketVector.entry (commonReserve C w) (allPacket C mask wins sample (i+1)))
    (allPolys mask wins sample (i+1)) B at ready
  change ReadyHeads (Function.update (allHeads H C (commonReserve C w) mask wins sample i) 29
      (allResult C (commonReserve C w) mask wins sample (i+1)++
        PacketVector.entry (commonReserve C w) (allPacket C mask wins sample (i+1))).length)
    (allResult C (commonReserve C w) mask wins sample (i+1)++
      PacketVector.entry (commonReserve C w) (allPacket C mask wins sample (i+1))).length at heads
  rw [hv] at actual ready
  rw [←allResult_succ] at actual ready heads
  have hout : Function.update (allHeads H C (commonReserve C w) mask wins sample i) 29
      (allResult C (commonReserve C w) mask wins sample ((i+1)+1)).length=
      allHeads H C (commonReserve C w) mask wins sample (i+1) := by
    simp only [allHeads,Function.update_idem]
  rw [hout] at actual heads
  refine ⟨B,actual.enlarge (workerBudget_mono C w (population+1) (n+1) (i+1) population (by omega)),?_,heads⟩
  exact ready.change_polys hpf.reserve (by have hd:=hpf.arithmetic;omega)
    (by rw [allPolys_length,allPolys_length])

end
end Theorem25Completion.WalkTranscriptColumn
