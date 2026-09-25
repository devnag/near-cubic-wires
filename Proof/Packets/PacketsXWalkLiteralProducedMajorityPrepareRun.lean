import Proof.Packets.PacketsXWalkLiteralProducedMajorityReady

/-! Closed physical preparation from raw header and actual walk words to
an initialized first-column majority state. No derived word is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open VectorBottomUp CloseoutRowsModeCache
noncomputable section
variable {population active depth n : Nat}
attribute [local irreducible] WalkLiteralProducedReserve.machine prefixMachine

def walk := TapeEmbedding.machine 176 WalkLiteralProducedReserve.machine
def prepare := Composition.machine walk prefixMachine
def prepareBudget (C w root population active depth n : Nat) (mask : List Bool) :=
  WalkLiteralProducedReserve.budget C w root population active depth n mask+1+prefixBudget C w population n

theorem prepare_run (C w d root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root (S C w) (R C w) wins)
    (hdepth : depth=SourceGradedRank.depth active)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (hVisits : n+1≤2^w) (hCodes : 2^(n+1)≤2^w) (codeTail : List Bool) :
    ∃masters work,Step prepare (prepareBudget C w root population active depth n (List.ofFn (fun i=>decide (i∈mask))))
      (fun _=>0)
      (input C w root population active n (List.ofFn (fun i=>decide (i∈mask)))
        (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
        (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
        (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail))
      (prefixHeads n) (prefixBank C w root mask wins sample codeTail masters work) ∧
      WalkLiteralProduced.Retained C (R C w) root population active (List.ofFn (fun i=>decide (i∈mask))) masters := by
  obtain ⟨masters,work,actual,_bound,ready,retained⟩:=WalkLiteralProducedReserve.run_retained C w d root mask wins
    h hdepth sample codeTail
  have first:=actual.embed (fun _ : Fin 176=>0) (fun _ : Fin 176=>[])
  have zeros : Fin.addCases (m:=566) (n:=176) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    refine Fin.addCases (m:=566) (n:=176) (fun j=>?_) (fun j=>?_) i <;>
      simp only [Fin.addCases_left,Fin.addCases_right]
  have first':=first.congr_in zeros rfl
  have last:=prefix_run C w d root mask wins h sample hVisits hCodes codeTail masters work ready
  exact ⟨masters,work,first'.seq last,retained⟩

end
end Theorem25Completion.WalkLiteralProducedMajority
