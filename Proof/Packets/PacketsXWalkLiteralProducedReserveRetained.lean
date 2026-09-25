import Proof.Packets.PacketsXWalkLiteralProducedReserveRun
import Proof.Packets.PacketsXWalkLiteralProducedRetainedRun

/-! A fixed ordinary walk program with no supplied reserve, palette, rank,
depth, workspace, or allocated transcript. Raw header/sample words suffice. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedReserve
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open VectorBottomUp CloseoutRowsModeCache
noncomputable section
attribute [local irreducible] setup WalkLiteralProduced.machine

variable {population active depth n : Nat}

theorem run_retained (C w d root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root (S C w) (R C w) wins)
    (hdepth : depth=SourceGradedRank.depth active)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) :
    ∃masters work,Step machine (budget C w root population active depth n (List.ofFn (fun i=>decide (i∈mask))))
      (fun _=>0)
      (input C w root population active n (List.ofFn (fun i=>decide (i∈mask)))
        (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
        (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
        (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail))
      (finalHeads n) (output C w root mask wins sample codeTail masters work) ∧
      (∀i,(work i).length ≤ S C w) ∧ TranscriptRewindReady (R C w) (S C w) (population+1) work ∧
      WalkLiteralProduced.Retained C (R C w) root population active (List.ofFn (fun i=>decide (i∈mask))) masters := by
  obtain ⟨masters,work,walk,bound,ready,retained⟩:=WalkLiteralProduced.run_retained C w d root (S C w) mask wins h hdepth sample codeTail
  refine ⟨masters,work,?_,bound,ready,retained⟩
  exact finish_run WalkLiteralProduced.machine C w root population active n (List.ofFn (fun i=>decide (i∈mask)))
    (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
    (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
    (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail) _ _ walk

end
end Theorem25Completion.WalkLiteralProducedReserve
