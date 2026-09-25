import Proof.Packets.MajorityCount
import Proof.Packets.UnaryCompareFlag

/-! Physical inclusive majority decision from the actual assignment bits.
The retained length and previously produced half-round-up threshold drive the
computation; no acceptance bit is input advice. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityAccept
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open Theorem25Completion

def H : Fin 6→Nat:=![0,0,1,0,0,0]
def A (R : Nat) (bits : List Bool) (count : Nat) (flag : Bool) : Fin 6→List Bool:=
  ![ZeroPadding.pad R bits,ZeroPadding.pad R (CompareMachine.word count),
    ZeroPadding.pad R (CompareMachine.word bits.length),List.replicate R false,
    ZeroPadding.pad R (CompareMachine.word ((bits.length+1)/2)),[flag]]
def countSlots : Fin 4→Fin 6:=![0,1,2,3]
def compareSlots : Fin 4→Fin 6:=![4,1,5,3]
noncomputable def count:=RecoveryFocus.machine countSlots MajorityCount.machine
noncomputable def compare:=RecoveryFocus.machine compareSlots UnaryCompareFlag.ready
noncomputable def machine:=Composition.machine count compare

theorem run (R : Nat) (bits : List Bool) (flag : Bool) (hR : 4*bits.length+5≤R) :
    Step machine (10*bits.length+21) H (A R bits 0 flag)
      H (A R bits (CycleCellBitCount.marks bits).length
        (decide ((bits.length+1)/2≤(CycleCellBitCount.marks bits).length))) := by
  have hn : (CycleCellBitCount.marks bits).length≤bits.length:=List.length_filter_le _ _
  have hz : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false:=by
    change ZeroPadding.pad R [false]=_
    simp only [ZeroPadding.pad,List.length_singleton,List.singleton_append]
    rw [←List.replicate_succ]
    congr 1
    omega
  have first : Step count (8*bits.length+12) H (A R bits 0 flag)
      H (A R bits (CycleCellBitCount.marks bits).length flag) := by
    apply PhysicalFocusBoundary.focus (MajorityCount.run bits R hR) countSlots (by decide) H H _ _
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>simp [countSlots,A,hz]
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>rfl
    · intro i away
      have hi : i≠1:=by intro he;subst i;exact away 1 rfl
      fin_cases i <;>simp_all [A]
  have second : Step compare (2*min ((bits.length+1)/2) (CycleCellBitCount.marks bits).length+8)
      H (A R bits (CycleCellBitCount.marks bits).length flag)
      H (A R bits (CycleCellBitCount.marks bits).length
        (decide ((bits.length+1)/2≤(CycleCellBitCount.marks bits).length))) := by
    apply PhysicalFocusBoundary.focus
      (UnaryCompareFlag.ready_run R ((bits.length+1)/2) (CycleCellBitCount.marks bits).length flag
        (by have:=Nat.min_le_right ((bits.length+1)/2) (CycleCellBitCount.marks bits).length;omega))
      compareSlots (by decide) H H _ _
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>rfl
    · intro i away
      have hi : i≠5:=by intro he;subst i;exact away 2 rfl
      fin_cases i <;>simp_all [A]
  exact (first.seq second).enlarge (by
    have:=Nat.min_le_right ((bits.length+1)/2) (CycleCellBitCount.marks bits).length
    omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityAccept
