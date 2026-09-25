import Proof.Packets.PacketsXWalkLiteralMastersData

/-! Paid palette master construction from raw numeric words and the actual mask.
Every derived scalar, template, padding cell and zero seed word is produced by execution. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Theorem25Completion.WalkLiteralMasters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Completion
noncomputable section

def slots1 : Fin 11→Fin 55 := ![0,7,8,9,10,11,12,13,14,15,16]
def phase1 := RecoveryFocus.machine slots1 (UnaryAffine.machine 2 3)
def bank1 (C R root rank depth M : Nat) (mask : List Bool) := install slots1 (input C R root rank depth M mask) (affineOutput C 2 3)
theorem bank1_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 11) :
    bank1 C R root rank depth M mask (slots1 i)=(affineOutput C 2 3) i :=
  install_slot slots1 (by decide) _ _ i
theorem bank1_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots1 j≠i) :
    bank1 C R root rank depth M mask i=input C R root rank depth M mask i := install_other slots1 _ _ _ hi

theorem join1 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,input C R root rank depth M mask (slots1 i)=(UnaryAffine.input C) i := by
  intro i;fin_cases i
  · change input C R root rank depth M mask 0=(UnaryAffine.input C) 0
    rfl
  · change input C R root rank depth M mask 7=(UnaryAffine.input C) 1
    rfl
  · change input C R root rank depth M mask 8=(UnaryAffine.input C) 2
    rfl
  · change input C R root rank depth M mask 9=(UnaryAffine.input C) 3
    rfl
  · change input C R root rank depth M mask 10=(UnaryAffine.input C) 4
    rfl
  · change input C R root rank depth M mask 11=(UnaryAffine.input C) 5
    rfl
  · change input C R root rank depth M mask 12=(UnaryAffine.input C) 6
    rfl
  · change input C R root rank depth M mask 13=(UnaryAffine.input C) 7
    rfl
  · change input C R root rank depth M mask 14=(UnaryAffine.input C) 8
    rfl
  · change input C R root rank depth M mask 15=(UnaryAffine.input C) 9
    rfl
  · change input C R root rank depth M mask 16=(UnaryAffine.input C) 10
    rfl

theorem step1 (C R root rank depth M : Nat) (mask : List Bool) : Step phase1 (UnaryAffine.budget C 2 3)
    (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank1 C R root rank depth M mask) := by
  have focused:=(affine_step C 2 3).focus slots1 (by decide) (fun _=>0) (input C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots1)
    (install_existing _ _ _ (join1 C R root rank depth M mask))).congr (zero_heads slots1) rfl
def joined1 := phase1
def budget1 (C R root rank depth M : Nat) (mask : List Bool) := UnaryAffine.budget C 2 3
theorem run1 (C R root rank depth M : Nat) (mask : List Bool) : Step joined1 (budget1 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank1 C R root rank depth M mask) := step1 C R root rank depth M mask

def slots2 : Fin 11→Fin 55 := ![0,17,18,19,20,21,22,23,24,25,26]
def phase2 := RecoveryFocus.machine slots2 (UnaryAffine.machine 1 9)
def bank2 (C R root rank depth M : Nat) (mask : List Bool) := install slots2 (bank1 C R root rank depth M mask) (affineOutput C 1 9)
theorem bank2_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 11) :
    bank2 C R root rank depth M mask (slots2 i)=(affineOutput C 1 9) i :=
  install_slot slots2 (by decide) _ _ i
theorem bank2_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots2 j≠i) :
    bank2 C R root rank depth M mask i=bank1 C R root rank depth M mask i := install_other slots2 _ _ _ hi

theorem join2 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank1 C R root rank depth M mask (slots2 i)=(UnaryAffine.input C) i := by
  intro i;fin_cases i
  · change bank1 C R root rank depth M mask 0=(UnaryAffine.input C) 0
    change bank1 C R root rank depth M mask (slots1 0)=_
    rw [bank1_slot]
    simpa [UnaryAffine.input,DimensionTemplate.input] using affine_source C 2 3
  · change bank1 C R root rank depth M mask 17=(UnaryAffine.input C) 1
    rw [bank1_other C R root rank depth M mask 17 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 18=(UnaryAffine.input C) 2
    rw [bank1_other C R root rank depth M mask 18 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 19=(UnaryAffine.input C) 3
    rw [bank1_other C R root rank depth M mask 19 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 20=(UnaryAffine.input C) 4
    rw [bank1_other C R root rank depth M mask 20 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 21=(UnaryAffine.input C) 5
    rw [bank1_other C R root rank depth M mask 21 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 22=(UnaryAffine.input C) 6
    rw [bank1_other C R root rank depth M mask 22 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 23=(UnaryAffine.input C) 7
    rw [bank1_other C R root rank depth M mask 23 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 24=(UnaryAffine.input C) 8
    rw [bank1_other C R root rank depth M mask 24 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 25=(UnaryAffine.input C) 9
    rw [bank1_other C R root rank depth M mask 25 (by decide)]
    rfl
  · change bank1 C R root rank depth M mask 26=(UnaryAffine.input C) 10
    rw [bank1_other C R root rank depth M mask 26 (by decide)]
    rfl

theorem step2 (C R root rank depth M : Nat) (mask : List Bool) : Step phase2 (UnaryAffine.budget C 1 9)
    (fun _=>0) (bank1 C R root rank depth M mask) (fun _=>0) (bank2 C R root rank depth M mask) := by
  have focused:=(affine_step C 1 9).focus slots2 (by decide) (fun _=>0) (bank1 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots2)
    (install_existing _ _ _ (join2 C R root rank depth M mask))).congr (zero_heads slots2) rfl
def joined2 := Composition.machine joined1 phase2
def budget2 (C R root rank depth M : Nat) (mask : List Bool) := budget1 C R root rank depth M mask+1+(UnaryAffine.budget C 1 9)
theorem run2 (C R root rank depth M : Nat) (mask : List Bool) : Step joined2 (budget2 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank2 C R root rank depth M mask) := (run1 C R root rank depth M mask).seq (step2 C R root rank depth M mask)
end
end Theorem25Completion.WalkLiteralMasters
