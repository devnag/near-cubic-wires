import Proof.Packets.PacketsXMajorityScalarNumericRaw

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

def templateBank (n : Nat) : Fin 10→List Bool:=![CompareMachine.word n,List.replicate (n+1) true,List.replicate (n+2) false,UnaryTemplate.tape (n+1),List.replicate (n+1+3) false,[],[],[],[],[]]
def templateSlots : Fin 3→Fin 10:=![1,3,4]
def templateMachine:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
theorem template_run (n : Nat) : Step templateMachine (2*(n+1)+8) (fun _=>0) (rawBank n)
    (fun _=>0) (templateBank n) := by
  apply PhysicalFocusBoundary.focus (CycleCommonReserve.of_clock (DimensionTemplate.ready false (n+1))) templateSlots (by decide)
    (fun _=>0) (fun _=>0) (rawBank n) (templateBank n)
  · intro i;rfl
  · intro i;fin_cases i <;>simp [rawBank,templateSlots,UWalkUnary.input,UWalkUnary.source,
      ZeroPadding.pad_zero,DimensionTemplate.input,unary_source,UnaryTemplate.tape,
      ZeroPadding.pad,CompareMachine.word]
  · intro i;rfl
  · intro i;fin_cases i <;>simp [templateBank,templateSlots,UWalkUnary.result,UWalkUnary.output,
      UWalkUnary.lead,UWalkUnary.source,ZeroPadding.pad_zero,DimensionTemplate.output,
      unary_source,UnaryTemplate.tape,ZeroPadding.pad,CompareMachine.word]
  · intro i away
    fin_cases i <;>first | (exfalso;exact away 0 rfl) | (exfalso;exact away 1 rfl) |
      (exfalso;exact away 2 rfl) | exact ⟨rfl,rfl⟩


end
end Completion.MajorityScalarNumeric
