import Proof.Packets.WindowProviderPorts

/-! Physical allocation or erasure of all private native-normalizer, raw
renaming and normalized-substitution words. Both reset logs are the already
produced arithmetic logs; each ordinary sweep retains its raw reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider.Workspace
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def workSlots (j : Fin 51) : Fin 256 :=
  if j.val<29 then ⟨j.val+96,by omega⟩ else
  if j.val<32 then ⟨j.val+97,by omega⟩ else
  if j.val<42 then ⟨j.val+98,by omega⟩ else ⟨j.val+99,by have h:=j.isLt;omega⟩
def slots : Fin 53→Fin 256 := Fin.addCases (m:=51) (n:=2) workSlots ![32,33]
def selected (i : Fin 256) : Prop :=
  (96≤ i.val ∧ i.val<125) ∨ (126≤ i.val ∧ i.val<129) ∨
  (130≤ i.val ∧ i.val<140) ∨ (141≤ i.val ∧ i.val<150)
instance (i : Fin 256) : Decidable (selected i) := inferInstanceAs (Decidable
  ((96≤ i.val ∧ i.val<125) ∨ (126≤ i.val ∧ i.val<129) ∨
    (130≤ i.val ∧ i.val<140) ∨ (141≤ i.val ∧ i.val<150)))
def cleared (R : Nat) (A : Fin 256→List Bool) (i : Fin 256) :=
  if selected i then List.replicate R false else A i
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 51)

theorem work_selected (j : Fin 51) : selected (workSlots j) := by
  unfold workSlots
  split
  · simp only [selected];omega
  · split
    · simp only [selected];omega
    · split <;>simp only [selected] <;>have h:=j.isLt <;>omega

theorem selected_work (i : Fin 256) (hi : selected i) : ∃j,workSlots j=i := by
  rcases hi with h|h|h|h
  · refine ⟨⟨i.val-96,by omega⟩,?_⟩
    apply Fin.ext
    simp only [workSlots,show i.val-96<29 by omega,if_true]
    omega
  · refine ⟨⟨i.val-97,by omega⟩,?_⟩
    apply Fin.ext
    simp only [workSlots,show ¬i.val-97<29 by omega,if_false,show i.val-97<32 by omega,if_true]
    omega
  · refine ⟨⟨i.val-98,by omega⟩,?_⟩
    apply Fin.ext
    simp only [workSlots,show ¬i.val-98<29 by omega,if_false,
      show ¬i.val-98<32 by omega,show i.val-98<42 by omega,if_true]
    omega
  · refine ⟨⟨i.val-99,by omega⟩,?_⟩
    apply Fin.ext
    simp only [workSlots,show ¬i.val-99<29 by omega,if_false,
      show ¬i.val-99<32 by omega,show ¬i.val-99<42 by omega]
    omega

theorem run (R : Nat) (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hH : ∀ j,H (slots j)=0)
    (hR : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false)
    (hfit : ∀ i,selected i→(A i).length≤R) :
    Step machine (2*R+4) H A H (cleared R A) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryScratchErase.erase_ready R (R+3)
    (fun j=>A (workSlots j)) (fun j=>hfit _ (work_selected j))
  have small : Step (RecoveryScratchErase.resetMachine 51) (2*R+4) (fun _=>0) _ (fun _=>0) _ :=
    ⟨r,hr,funext hh,ht,hs.le⟩
  apply PhysicalFocusBoundary.focus small slots (by decide) H H A (cleared R A)
  · intro j;exact (hH j).symm
  · intro j
    refine Fin.addCases (m:=51) (n:=2) (fun k=>?_) (fun k=>?_) j
    · rw [slots,Fin.addCases_left]
      have ek : k.castAdd 2=(k.castAdd 1).castAdd 1 := rfl
      rw [ek,Fin.addCases_left,Fin.addCases_left]
    · rw [slots,Fin.addCases_right]
      fin_cases k
      · simpa [Fin.addCases] using hR.symm
      · simpa [Fin.addCases] using hlog.symm
  · intro j;exact (hH j).symm
  · intro j
    refine Fin.addCases (m:=51) (n:=2) (fun k=>?_) (fun k=>?_) j
    · rw [slots,Fin.addCases_left]
      have ek : k.castAdd 2=(k.castAdd 1).castAdd 1 := rfl
      rw [ek,Fin.addCases_left,Fin.addCases_left,cleared,if_pos (work_selected k)]
    · rw [slots,Fin.addCases_right]
      fin_cases k
      · simpa [cleared,selected,Fin.addCases] using hR.symm
      · simpa [cleared,selected,Fin.addCases,Nat.max_eq_left (by omega : R+1≤R+3)] using hlog.symm
  · intro i away
    have hn : ¬selected i := by
      intro hi
      obtain ⟨j,hj⟩:=selected_work i hi
      exact away (j.castAdd 2) ((Fin.addCases_left j).trans hj)
    exact ⟨rfl,by simp only [cleared,if_neg hn]⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider.Workspace
