import Proof.Packets.PhysicalOneOutput

/-! Paid allocation or erasure of one ambient word from an actual retained
raw reserve and erase log, preserving all other tapes and cursors. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalEraseInto
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def slots {t : Nat} (target raw log : Fin t) : Fin 3→Fin t := ![target,raw,log]
noncomputable def machine {t : Nat} (target raw log : Fin t) :=
  RecoveryFocus.machine (slots target raw log) (RecoveryScratchErase.resetMachine 1)

theorem run {t : Nat} (R : Nat) (target raw log : Fin t)
    (htr : target≠raw) (htl : target≠log) (hrl : raw≠log)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (ht : H target=0) (hr : H raw=0) (hl : H log=0)
    (hraw : A raw=List.replicate R true) (hlog : A log=List.replicate (R+3) false)
    (hfit : (A target).length≤R) :
    Step (machine target raw log) (2*R+4) H A H (Function.update A target (List.replicate R false)) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3)
    (fun _ : Fin 1=>A target) (fun _=>hfit))
  have he : max (R+3) (R+1)=R+3 := by omega
  rw [he] at h
  let localA : Fin 3→List Bool := ![A target,List.replicate R true,List.replicate (R+3) false]
  have small : Step (RecoveryScratchErase.resetMachine 1) (2*R+4) (fun _=>0) localA
      (fun _=>0) (Function.update localA 0 (List.replicate R false)) := by
    convert h using 1 <;>first | rfl | (funext i;fin_cases i <;>rfl)
  have hinj : Function.Injective (slots target raw log) := by
    intro i j he
    fin_cases i <;>fin_cases j <;>simp_all [slots]
  exact PhysicalOneOutput.focus _ _ _ 0 _ small (slots target raw log) hinj H A
    (by intro i;fin_cases i <;>first | exact ht | exact hr | exact hl)
    (by intro i;fin_cases i <;>first | rfl | exact hraw | exact hlog)

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalEraseInto
