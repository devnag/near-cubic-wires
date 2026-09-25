import Proof.Packets.PacketsXWalkLiteralProducedReservePrepare
import Proof.Packets.PacketsXWalkLiteralProducedReserveLayout

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

theorem prepared_reassemble (C w root population active n : Nat) (mask x y code : List Bool) :
    Fin.addCases (m:=433) (n:=133) (motive:=fun _=>List Bool)
      (WalkLiteralProduced.input C (R C w) root population active (S C w) n mask x y code)
      (fun j=>prepared C w root population active n mask x y code (j.natAdd 433))=
      prepared C w root population active n mask x y code := by
  funext i
  refine Fin.addCases (m:=433) (n:=133) (fun j=>?_) (fun j=>?_) i
  · rw [Fin.addCases_left]
    exact (prepared_view C w root population active n mask x y code j).symm
  · rw [Fin.addCases_right]

theorem finish_run {st fuel : Nat} (worker : Machine 433 st)
    (C w root population active n : Nat) (mask x y code : List Bool)
    (H : Fin 433→Nat) (A : Fin 433→List Bool)
    (localRun : Step worker fuel (fun _=>0)
      (WalkLiteralProduced.input C (R C w) root population active (S C w) n mask x y code) H A) :
    Step (Composition.machine setup (TapeEmbedding.machine 133 worker)) (setupBudget C w+1+fuel)
      (fun _=>0) (input C w root population active n mask x y code)
      (Fin.addCases (m:=433) (n:=133) (motive:=fun _=>Nat) H (fun _=>0))
      (Fin.addCases (m:=433) (n:=133) (motive:=fun _=>List Bool) A
        (fun j=>prepared C w root population active n mask x y code (j.natAdd 433))) := by
  have last:=localRun.embed (fun _ : Fin 133=>0)
    (fun j=>prepared C w root population active n mask x y code (j.natAdd 433))
  have zeros : Fin.addCases (m:=433) (n:=133) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    refine Fin.addCases (m:=433) (n:=133) (fun j=>?_) (fun j=>?_) i <;>
      simp only [Fin.addCases_left,Fin.addCases_right]
  have last':=last.congr_in zeros (prepared_reassemble C w root population active n mask x y code)
  exact (setup_run C w root population active n mask x y code).seq last'

def machine := Composition.machine setup (TapeEmbedding.machine 133 WalkLiteralProduced.machine)
def budget (C w root population active depth n : Nat) (mask : List Bool) :=
  setupBudget C w+1+WalkLiteralProduced.budget C w root population active depth (S C w) n mask

def finalHeads (n : Nat) : Fin 566→Nat :=
  Fin.addCases (m:=433) (n:=133) (motive:=fun _=>Nat) (WalkLiteralProduced.finalHeads n) (fun _=>0)

variable {population active depth n : Nat}
def output (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) : Fin 566→List Bool :=
  Fin.addCases (m:=433) (n:=133) (motive:=fun _=>List Bool)
    (install WalkLiteralProduced.coldSlots
      (WalkLiteralProduced.prepared masters (canonicalGradedRank population active) (R C w) (S C w) n
        (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
        (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
        (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralLoop.A C w root (S C w) (R C w) mask wins sample
          (WalkLiteralMasters.zeroSeed (canonicalGradedRank population active)) codeTail [] [] (n+1) work)
        (fun _=>CompareMachine.word n)))
    (fun j=>prepared C w root population active n (List.ofFn (fun i=>decide (i∈mask)))
      (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
      (WalkLiteralProduced.coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
      (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail) (j.natAdd 433))

end
end Theorem25Completion.WalkLiteralProducedReserve
