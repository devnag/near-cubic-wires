import Proof.Rows.PowerFactorAway

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_PowerMoves
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey PCJ45bee56da9f34d5a_PowerBank
noncomputable section

def copySlots (s t : Fin 94) : Fin 4→Fin 94 := ![s,t,31,32]
def copy (s t : Fin 94) := RecoveryFocus.machine (copySlots s t) MatrixFrameCopy.machine

theorem copy_run (s t : Fin 94) (hi : Function.Injective (copySlots s t)) (bits backing : List Bool)
    (U : Nat) (hb : backing.length ≤ 2*bits.length+1) (hU : 4*bits.length+3 ≤ U)
    (H : Fin 94→Nat) (A : Fin 94→List Bool)
    (hh : ∀i,H (copySlots s t i)=0) (hs : A s=ZeroPadding.pad U (frame bits))
    (ht : A t=ZeroPadding.pad U backing) (h31 : A 31=List.replicate U false) (h32 : A 32=List.replicate U false) :
    Step (copy s t) (8*bits.length+8) H A H (Function.update A t (ZeroPadding.pad U (frame bits))) := by
  have h := (PCJ45bee56da9f34d5a_ScalarReplace.run bits backing U hb hU).dock (copySlots s t) hi H A hh
    (by intro i;fin_cases i <;>assumption)
  apply h.congr
  · exact dockH_existing _ _ _ hh
  · apply HierarchyAllocation.install_eq (copySlots s t) hi
    · intro i;fin_cases i
      · have hn : s≠t := fun he=>by have bad : (0 : Fin 4)=1:=hi he;cases bad
        exact (Function.update_of_ne hn _ _).trans hs
      · exact Function.update_self _ _ _
      · have hn : (31 : Fin 94)≠t := fun he=>by have bad : (2 : Fin 4)=1:=hi he;cases bad
        exact (Function.update_of_ne hn _ _).trans h31
      · have hn : (32 : Fin 94)≠t := fun he=>by have bad : (3 : Fin 4)=1:=hi he;cases bad
        exact (Function.update_of_ne hn _ _).trans h32
    · intro i hn;exact Function.update_of_ne (fun he=>hn 1 he.symm) _ _

def loadBase := copy 92 0
def replaceFactor := copy 93 28

theorem load_run (a B p w F U q pos : Nat) (source out : List Bool) (hU : 4*w+3 ≤ U) :
    Step loadBase (8*w+8) (heads pos out.length 0)
      (bank a B p w F U q source out (List.replicate U false) [])
      (heads pos out.length 0)
      (bank a B p w F U q source out (ZeroPadding.pad U (frame (binary w B))) []) := by
  have h := copy_run 92 0 (by decide) (binary w B) [] U (by simp) (by simpa only [binary_length] using hU)
    (heads pos out.length 0) (bank a B p w F U q source out (List.replicate U false) [])
    (by intro i;fin_cases i <;>rfl) rfl (ZeroPadding.pad_zero _) (ZeroPadding.pad_zero _) (ZeroPadding.pad_zero _)
  simp only [binary_length] at h
  apply h.congr rfl
  funext i
  by_cases hi:i=0
  · subst i
    rw [Function.update_self]
    exact (ZeroPadding.pad_zero _).symm
  · rw [Function.update_of_ne hi]
    by_cases ht:i=93
    · subst i;rfl
    · exact bank_away a B p w F U q source out _ _ [] [] i hi ht

theorem replace_run (a a' B p w F U q pos : Nat) (source out coefficient : List Bool) (hU : 4*w+3 ≤ U) :
    Step replaceFactor (8*w+8) (heads pos out.length 0)
      (bank a B p w F U q source out coefficient (frame (binary w a')))
      (heads pos out.length 0)
      (bank a' B p w F U q source out coefficient (frame (binary w a'))) := by
  have h := copy_run 93 28 (by decide) (binary w a') (frame (binary w a)) U
    (by simp [frame_length,binary_length]) (by simpa only [binary_length] using hU)
    (heads pos out.length 0) (bank a B p w F U q source out coefficient (frame (binary w a')))
    (by intro i;fin_cases i <;>rfl) rfl rfl (ZeroPadding.pad_zero _) (ZeroPadding.pad_zero _)
  simp only [binary_length] at h
  apply h.congr rfl
  funext i
  by_cases hi:i=28
  · subst i;rfl
  · rw [Function.update_of_ne hi]
    exact factor_away a a' B p w F U q source out coefficient (frame (binary w a')) i hi
end
end PCJ45bee56da9f34d5a_PowerMoves
