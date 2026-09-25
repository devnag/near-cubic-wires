import Proof.Packets.PacketsXWalkTranscriptColumnAllNext
import Proof.Packets.WalkTranscriptColumnExists

/-! The complete physical all-candidate consumer. It consumes column zero
once, then the actual retained population word drives extraction, majority,
append and reset for the remaining candidates. The final bank contains the
original walk-coordinate polynomials in increasing candidate order. -/
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

def allMachine := WalkTranscriptColumnController.firstThenRemaining candidate worker
def allBudget (C w population T : Nat) := candidateBudget C w T 0+1+
  WalkTranscriptColumnController.budget population (workerBudget C w (population+1) T population)

theorem all_run (palette : Fin 10→List Bool) (C w d root S L : Nat)
    (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (hfit : (population+1)^(d*(n+1))≤2^w) (hVisits : n+1≤2^w) (hCodes : 2^(n+1)≤2^w)
    (hc : MajorityComplete.Bootstrap.Compatible palette C (commonReserve C w) (n+1) ((commonReserve C w)^2))
    (H : Fin 471→Nat) (A : Fin 471→List Bool) (hh : ReadyHeads H 0)
    (ha : Ready palette C (commonReserve C w) ((commonReserve C w)^2) (population+1) (n+1) S 0
      (PacketTranscript.prefixBank (commonReserve C w) (WalkLiteralLoop.rows C mask wins sample) (n+1))
      (allLast C mask wins sample 0) (OrderedPacketStep.bank C (commonReserve C w) (allPolys mask wins sample 0))
      [] (allPolys mask wins sample 0) A) :
    let R:=commonReserve C w
    ∃B,Step allMachine (allBudget C w population (n+1))
        (Function.update (WalkTranscriptColumnController.heads H) 29 0)
        (WalkTranscriptColumnController.tapes R population A)
        (WalkTranscriptColumnController.heads (allHeads H C R mask wins sample population))
        (WalkTranscriptColumnController.tapes R population B) ∧
      (WalkTranscriptColumnController.tapes R population B) 471=
        PacketVector.bank R (List.ofFn (fun column : Fin (population+1)=>
          (Normalized.structuralMaskedWalkListCoordinate mask (canonicalGradedLabel population active)
            wins 0 sample column).map (maskNat C))) ∧
      AllReady palette C R S mask wins sample population B := by
  dsimp only
  let P (i : Nat) (a : Fin 471→List Bool) :=
    AllReady palette C (commonReserve C w) S mask wins sample i a ∧
      ReadyHeads (allHeads H C (commonReserve C w) mask wins sample i)
        (allResult C (commonReserve C w) mask wins sample (i+1)).length
  have firstStep : ∃a,Step candidate (candidateBudget C w (n+1) 0) H A
      (allHeads H C (commonReserve C w) mask wins sample 0) a ∧ P 0 a := by
    exact all_first_run palette C w d root S L mask wins h sample hfit hVisits hCodes hc H A hh ha
  have nextStep : ∀i,i<population→∀a,P i a→∃b,
      Step worker (workerBudget C w (population+1) (n+1) population)
        (allHeads H C (commonReserve C w) mask wins sample i) a
        (allHeads H C (commonReserve C w) mask wins sample (i+1)) b ∧ P (i+1) b := by
    intro i hi a ha
    exact all_next_run palette C w d root S L mask wins h sample hfit hVisits hCodes hc H i hi a ha.2 ha.1
  obtain ⟨B,actual,hB⟩:=WalkTranscriptColumnController.first_then_remaining_exists candidate worker
    (candidateBudget C w (n+1) 0) (commonReserve C w) population
    (workerBudget C w (population+1) (n+1) population) H A
    (allHeads H C (commonReserve C w) mask wins sample) P firstStep nextStep
  refine ⟨B,actual,?_,hB.1⟩
  rw [WalkTranscriptColumnController.result_tapes]
  exact hB.1.result.trans (allResult_final C (commonReserve C w) mask wins sample)

end
end Theorem25Completion.WalkTranscriptColumn
