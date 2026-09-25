import Proof.Packets.SubstitutionOuterLoop

/-! Physically allocate or clear all nine substitution scratch tapes35..43.
The atom bank34, arithmetic arena, raw reserve, and reset log are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScratch
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def slots : Fin 11→Fin 44 := Fin.addCases (m:=9) (n:=2) (fun j=>j.natAdd 35) ![32,33]
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 9)
def cleared (R : Nat) (A : Fin 44→List Bool) (i : Fin 44) :=
  if 35 ≤ i.val then List.replicate R false else A i

theorem slots_work (j : Fin 9) : slots (j.castAdd 2)=j.natAdd 35 := Fin.addCases_left _
theorem slots_reserve (j : Fin 2) : slots (j.natAdd 9)=(![32,33] : Fin 2→Fin 44) j := Fin.addCases_right _

theorem run (R : Nat) (H : Fin 44→Nat) (A : Fin 44→List Bool)
    (hH : ∀ j,H (slots j)=0)
    (hR : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false)
    (hfit : ∀ i,35 ≤ i.val→(A i).length≤R) :
    Step machine (2*R+4) H A H (cleared R A) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryScratchErase.erase_ready R (R+3)
    (fun j : Fin 9=>A (j.natAdd 35)) (fun j=>hfit _ (by simp))
  have small : Step (RecoveryScratchErase.resetMachine 9) (2*R+4) (fun _=>0) _ (fun _=>0) _ :=
    ⟨r,hr,funext hh,ht,hs.le⟩
  apply PhysicalFocusBoundary.focus small slots (by decide) H H A (cleared R A)
  · intro j;exact (hH j).symm
  · intro j
    refine Fin.addCases (m:=9) (n:=2) (fun k=>?_) (fun k=>?_) j
    · rw [slots_work]
      have ek : k.castAdd 2=(k.castAdd 1).castAdd 1 := rfl
      rw [ek,Fin.addCases_left,Fin.addCases_left]
    · rw [slots_reserve]
      fin_cases k
      · simpa [Fin.addCases] using hR.symm
      · simpa [Fin.addCases] using hlog.symm
  · intro j;exact (hH j).symm
  · intro j
    refine Fin.addCases (m:=9) (n:=2) (fun k=>?_) (fun k=>?_) j
    · rw [slots_work]
      have ek : k.castAdd 2=(k.castAdd 1).castAdd 1 := rfl
      rw [ek,Fin.addCases_left,Fin.addCases_left]
      simp [cleared]
    · rw [slots_reserve]
      fin_cases k
      · simpa [cleared,Fin.addCases] using hR.symm
      · simpa [cleared,Fin.addCases,Nat.max_eq_left (by omega : R+1≤R+3)] using hlog.symm
  · intro i away
    refine ⟨rfl,?_⟩
    have hi : ¬35 ≤ i.val := by
      intro hn
      let j : Fin 9:=⟨i.val-35,by have h:=i.isLt;omega⟩
      apply away (j.castAdd 2)
      rw [slots_work]
      apply Fin.ext
      dsimp [j]
      omega
    simp [cleared,hi]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScratch
