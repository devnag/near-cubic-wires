import Proof.Packets.PacketsXWindowModeCacheDock
import Proof.Packets.ReusableNormalizedArithmetic

/-! The concrete mode-cache call preserves the arithmetic engine and every
provider field outside its fixed tape selection. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache

theorem mode_output_outside (p : Parameters) (M R : Nat) (A : Fin 256 → List Bool)
    (i : Fin 256) (hi : ∀j,modePorts j≠i) : modeOutput p M R A i=A i := by
  cases hp : RecoveryFocus.pick modePorts i with
  | none => simp only [modeOutput,PhysicalFocusBoundary.dock,hp]
  | some j => exact False.elim (hi j (RecoveryFocus.slot_of_pick modePorts hp))

theorem mode_output_engine (p : Parameters) (M C R : Nat)
    (left right : List (List Bool)) (A : Fin 256 → List Bool)
    (ha : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    ∀i : Fin 34,modeOutput p M R A (i.castAdd 222)=
      ReusableArithmetic.state C R left right i := by
  intro i
  by_cases hi : i.val<30
  · rw [mode_output_outside p M R A (i.castAdd 222) (by
      intro j he
      have h:=congrArg (fun k : Fin 256=>k.val) he
      fin_cases j <;> norm_num [modePorts] at h <;> omega)]
    exact ha i
  · have cases : i=30 ∨ i=31 ∨ i=32 ∨ i=33 := by
      have h:=i.isLt
      omega
    rcases cases with rfl|rfl|rfl|rfl
    · change modeOutput p M R A (modePorts 25)=List.replicate (R+3) false
      simp [modeOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot modePorts mode_injective,
        ModeCacheReady.A,ModeCacheReady.caps,reuseData,Fin.addCases,ZeroPadding.pad_zero]
    · change modeOutput p M R A (modePorts 28)=UnaryTemplate.tape R
      simp [modeOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot modePorts mode_injective,
        ModeCacheReady.A,Fin.addCases]
    · change modeOutput p M R A (modePorts 26)=List.replicate R true
      simp [modeOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot modePorts mode_injective,
        ModeCacheReady.A,ModeCacheReady.caps,reuseData,Fin.addCases,ZeroPadding.pad_zero]
    · change modeOutput p M R A (modePorts 27)=List.replicate (R+3) false
      simp [modeOutput,PhysicalFocusBoundary.dock,RecoveryFocus.pick_slot modePorts mode_injective,
        ModeCacheReady.A,ModeCacheReady.caps,reuseData,Fin.addCases,
        Rewind.Workspace.pad_zeros,Nat.max_eq_left (by omega : R+1 ≤ R+3)]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
