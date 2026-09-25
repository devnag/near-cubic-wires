import Proof.Packets.PacketsXMajorityScalarNumericTemplate

/-! Paid majority scalar arithmetic from the retained comparison word for n.
The sample count is N=n+1. Every destination and reset log starts empty. -/
set_option autoImplicit false
set_option maxHeartbeats 80000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.MajorityScalarNumeric
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Theorem25Completion
noncomputable section

def compareBank (n : Nat) : Fin 10→List Bool:=![CompareMachine.word n,List.replicate (n+1) true,List.replicate (n+2) false,UnaryTemplate.tape (n+1),List.replicate (n+1+3) false,CompareMachine.word (n+1),List.replicate (n+1+2) false,[],[],[]]
def compareSlots : Fin 3→Fin 10:=![3,5,6]
def compareMachine:=RecoveryFocus.machine compareSlots (UWalkUnary.machine true false)
theorem compare_input (n : Nat) (i : Fin 3) :
    UWalkUnary.input (n+1+2) (n+1) i=templateBank n (compareSlots i) := by
  fin_cases i
  · change UWalkUnary.source (n+1+2) (n+1)=templateBank n ⟨3,by decide⟩
    simp only [templateBank,Matrix.cons_val_zero',Matrix.cons_val_succ',unary_source]
  · change ([] : List Bool)=templateBank n ⟨5,by decide⟩
    simp only [templateBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · change ([] : List Bool)=templateBank n ⟨6,by decide⟩
    simp only [templateBank,Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem compare_output (n : Nat) (i : Fin 3) :
    UWalkUnary.result true false (n+1+2) (n+1) i=compareBank n (compareSlots i) := by
  fin_cases i
  · change UWalkUnary.source (n+1+2) (n+1)=compareBank n ⟨3,by decide⟩
    simp only [compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ',unary_source]
  · change UWalkUnary.output true false (n+1)=compareBank n ⟨5,by decide⟩
    simp only [compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
    rfl
  · change List.replicate (n+1+2) false=compareBank n ⟨6,by decide⟩
    simp only [compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem compare_other (n : Nat) (i : Fin 10) (away : ∀j,compareSlots j≠i) :
    templateBank n i=compareBank n i := by
  fin_cases i
  · simp only [templateBank,compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · simp only [templateBank,compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · simp only [templateBank,compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact False.elim (away 0 rfl)
  · simp only [templateBank,compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact False.elim (away 1 rfl)
  · exact False.elim (away 2 rfl)
  · simp only [templateBank,compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · simp only [templateBank,compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · simp only [templateBank,compareBank,Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem compare_run (n : Nat) : Step compareMachine (2*(n+1)+6) (fun _=>0) (templateBank n)
    (fun _=>0) (compareBank n) := by
  exact PhysicalFocusBoundary.focus
    (CycleCommonReserve.of_clock (UWalkUnary.ready true false (n+1+2) (n+1)))
    compareSlots (by decide) (fun _=>0) (fun _=>0) (templateBank n) (compareBank n)
    (fun _=>rfl) (compare_input n) (fun _=>rfl) (compare_output n)
    (fun i away=>⟨rfl,compare_other n i away⟩)

end
end Completion.MajorityScalarNumeric
