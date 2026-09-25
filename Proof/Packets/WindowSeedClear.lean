import Proof.Packets.WindowSeedPrimitives
import Proof.Packets.PhysicalOneOutput

/-! Actual allocation/reentry clearing of every private window field. The
shared raw reserve and erase log, and all seven actual metadata masters,
are retained. The same machine accepts blank or previously used capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def privateSlot (j : Fin 60) : Fin 69 :=
  if h:j.val<50 then ⟨j.val,by omega⟩ else ⟨j.val+2,by omega⟩
def clearSlots : Fin 62→Fin 69 := Fin.addCases (m:=60) (n:=2) privateSlot ![50,51]
def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 60)
def cleared (R : Nat) (A : Fin 69→List Bool) (i : Fin 69) : List Bool :=
  if i.val<62 ∧ i≠50 ∧ i≠51 then List.replicate R false else A i

theorem clear_run (R : Nat) (A : Fin 69→List Bool)
    (hraw : A 50=List.replicate R true) (hlog : A 51=List.replicate (R+3) false)
    (hfit : ∀j,(A (privateSlot j)).length≤R) :
    Step clear (2*R+4) (fun _=>0) A (fun _=>0) (cleared R A) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3) (fun j : Fin 60=>A (privateSlot j)) hfit)
  have hmax : max (R+3) (R+1)=R+3 := by omega
  rw [hmax] at h
  apply PhysicalFocusBoundary.focus h clearSlots (by decide) (fun _=>0) (fun _=>0) A (cleared R A)
  · intro j;rfl
  · intro j
    fin_cases j <;>first | rfl | exact hraw.symm | exact hlog.symm
  · intro j;rfl
  · intro j
    fin_cases j <;>simp [clearSlots,privateSlot,cleared,Fin.addCases,hraw,hlog]
  · intro i away
    have hi : ¬(i.val<62 ∧ i≠50 ∧ i≠51) := by
      rintro ⟨hlt,h50,h51⟩
      have hn50 : i.val≠50 := by intro he;apply h50;exact Fin.ext he
      have hn51 : i.val≠51 := by intro he;apply h51;exact Fin.ext he
      by_cases hsmall:i.val<50
      · let j : Fin 60:=⟨i.val,by omega⟩
        apply away (j.castAdd 2)
        apply Fin.ext
        simp [clearSlots,privateSlot,j,Fin.addCases,hsmall,show i.val<60 by omega]
      · let j : Fin 60:=⟨i.val-2,by omega⟩
        apply away (j.castAdd 2)
        apply Fin.ext
        simp [clearSlots,privateSlot,j,Fin.addCases,show ¬i.val-2<50 by omega,show i.val-2<60 by omega]
        omega
    exact ⟨rfl,by simp only [cleared,if_neg hi]⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
