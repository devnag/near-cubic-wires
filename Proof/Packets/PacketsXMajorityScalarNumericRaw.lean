import Proof.Packets.CycleCommonReserve
import Proof.Packets.PacketsXMajorityScalarSeed
import Proof.Packets.PhysicalPrepend
import Proof.Rows.SourceDockCore

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

theorem unary_source (N : Nat) : UWalkUnary.source (N+2) N=UnaryTemplate.tape N := by
  simp [UWalkUnary.source,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

def input (n : Nat) : Fin 10→List Bool:=![CompareMachine.word n,[],[],[],[],[],[],[],[],[]]

def rawBank (n : Nat) : Fin 10→List Bool:=![CompareMachine.word n,List.replicate (n+1) true,List.replicate (n+2) false,[],[],[],[],[],[],[]]
def rawSlots : Fin 3→Fin 10:=![0,1,2]
def rawMachine:=RecoveryFocus.machine rawSlots (UWalkUnary.machine false true)
theorem raw_run (n : Nat) : Step rawMachine (2*n+6) (fun _=>0) (input n)
    (fun _=>0) (rawBank n) := by
  apply PhysicalFocusBoundary.focus (CycleCommonReserve.of_clock (UWalkUnary.ready false true 0 n)) rawSlots (by decide)
    (fun _=>0) (fun _=>0) (input n) (rawBank n)
  · intro i;rfl
  · intro i;fin_cases i <;>simp [input,rawSlots,UWalkUnary.input,UWalkUnary.source,
      ZeroPadding.pad_zero,DimensionTemplate.input,unary_source,UnaryTemplate.tape,
      ZeroPadding.pad,CompareMachine.word]
  · intro i;rfl
  · intro i;fin_cases i <;>simp [rawBank,rawSlots,UWalkUnary.result,UWalkUnary.output,
      UWalkUnary.lead,UWalkUnary.source,ZeroPadding.pad_zero,DimensionTemplate.output,
      unary_source,UnaryTemplate.tape,ZeroPadding.pad,CompareMachine.word]
  · intro i away
    fin_cases i <;>first | (exfalso;exact away 0 rfl) | (exfalso;exact away 1 rfl) |
      (exfalso;exact away 2 rfl) | exact ⟨rfl,rfl⟩


end
end Completion.MajorityScalarNumeric
