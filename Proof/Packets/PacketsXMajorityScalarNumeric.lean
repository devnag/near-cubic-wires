import Proof.Packets.PacketsXMajorityScalarNumericCompare

/-! Paid majority scalar arithmetic from the retained comparison word for n.
The sample count is N=n+1. Every destination and reset log starts empty. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.MajorityScalarNumeric
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Theorem25Completion
noncomputable section

def thresholdBank (n k : Nat) : Fin 10→List Bool:=![CompareMachine.word n,List.replicate (n+1) true,List.replicate (n+2) false,UnaryTemplate.tape (n+1),List.replicate (n+1+3) false,CompareMachine.word (n+1),List.replicate (n+1+2) false,CompareMachine.word ((n+1+1)/2),List.replicate k false,[]]
def thresholdSlots : Fin 3→Fin 10:=![5,7,8]
def thresholdMachine:=RecoveryFocus.machine thresholdSlots MajorityScalarSeed.thresholdMachine

theorem threshold_run (n : Nat) : ∃ k≤n+1+2,
    Step thresholdMachine (2*(n+1)+6) (fun _=>0) (compareBank n)
      (fun _=>0) (thresholdBank n k) := by
  obtain ⟨k,hk,h⟩:=MajorityScalarSeed.threshold_run (n+1)
  refine ⟨k,hk,?_⟩
  apply PhysicalFocusBoundary.focus h thresholdSlots (by decide)
    (fun _=>0) (fun _=>0) (compareBank n) (thresholdBank n k)
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    fin_cases i
    · refine ⟨rfl,?_⟩
      simp only [compareBank,thresholdBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · refine ⟨rfl,?_⟩
      simp only [compareBank,thresholdBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · refine ⟨rfl,?_⟩
      simp only [compareBank,thresholdBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · refine ⟨rfl,?_⟩
      simp only [compareBank,thresholdBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · refine ⟨rfl,?_⟩
      simp only [compareBank,thresholdBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · exact False.elim (away 0 rfl)
    · refine ⟨rfl,?_⟩
      simp only [compareBank,thresholdBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · exact False.elim (away 1 rfl)
    · exact False.elim (away 2 rfl)
    · refine ⟨rfl,?_⟩
      simp only [compareBank,thresholdBank,Matrix.cons_val_zero',Matrix.cons_val_succ']

def machine1:=Composition.machine rawMachine templateMachine
def machine2:=Composition.machine machine1 compareMachine
def machine:=Composition.machine machine2 thresholdMachine
def budget (n : Nat):=(2*n+6)+1+(2*(n+1)+8)+1+(2*(n+1)+6)+1+(2*(n+1)+6)
theorem run (n : Nat) : ∃ k≤n+1+2,
    Step machine (budget n) (fun _=>0) (input n) (fun _=>0) (thresholdBank n k) := by
  obtain ⟨k,hk,h⟩:=threshold_run n
  exact ⟨k,hk,(((raw_run n).seq (template_run n)).seq (compare_run n)).seq h⟩

end
end Completion.MajorityScalarNumeric
