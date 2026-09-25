import Proof.Packets.PacketsXWalkLiteralMastersArithmetic

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

def slots3 : Fin 3→Fin 55 := ![0,27,28]
def phase3 := RecoveryFocus.machine slots3 (DimensionTemplate.machine false)
def bank3 (C R root rank depth M : Nat) (mask : List Bool) := install slots3 (bank2 C R root rank depth M mask) (DimensionTemplate.output false (C))
theorem bank3_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 3) :
    bank3 C R root rank depth M mask (slots3 i)=(DimensionTemplate.output false (C)) i :=
  install_slot slots3 (by decide) _ _ i
theorem bank3_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots3 j≠i) :
    bank3 C R root rank depth M mask i=bank2 C R root rank depth M mask i := install_other slots3 _ _ _ hi

theorem join3 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank2 C R root rank depth M mask (slots3 i)=(DimensionTemplate.input (C)) i := by
  intro i;fin_cases i
  · change bank2 C R root rank depth M mask 0=(DimensionTemplate.input (C)) 0
    change bank2 C R root rank depth M mask (slots2 0)=_
    rw [bank2_slot]
    simpa [UnaryAffine.input,DimensionTemplate.input] using affine_source C 1 9
  · change bank2 C R root rank depth M mask 27=(DimensionTemplate.input (C)) 1
    rw [bank2_other C R root rank depth M mask 27 (by decide)]
    rw [bank1_other C R root rank depth M mask 27 (by decide)]
    rfl
  · change bank2 C R root rank depth M mask 28=(DimensionTemplate.input (C)) 2
    rw [bank2_other C R root rank depth M mask 28 (by decide)]
    rw [bank1_other C R root rank depth M mask 28 (by decide)]
    rfl

theorem step3 (C R root rank depth M : Nat) (mask : List Bool) : Step phase3 (2*(C)+8)
    (fun _=>0) (bank2 C R root rank depth M mask) (fun _=>0) (bank3 C R root rank depth M mask) := by
  have focused:=(CycleCommonReserve.of_clock (DimensionTemplate.ready false (C))).focus slots3 (by decide) (fun _=>0) (bank2 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots3)
    (install_existing _ _ _ (join3 C R root rank depth M mask))).congr (zero_heads slots3) rfl
def joined3 := Composition.machine joined2 phase3
def budget3 (C R root rank depth M : Nat) (mask : List Bool) := budget2 C R root rank depth M mask+1+(2*(C)+8)
theorem run3 (C R root rank depth M : Nat) (mask : List Bool) : Step joined3 (budget3 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank3 C R root rank depth M mask) := (run2 C R root rank depth M mask).seq (step3 C R root rank depth M mask)

def slots4 : Fin 3→Fin 55 := ![15,29,30]
def phase4 := RecoveryFocus.machine slots4 (DimensionTemplate.machine false)
def bank4 (C R root rank depth M : Nat) (mask : List Bool) := install slots4 (bank3 C R root rank depth M mask) (DimensionTemplate.output false (2*C+3))
theorem bank4_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 3) :
    bank4 C R root rank depth M mask (slots4 i)=(DimensionTemplate.output false (2*C+3)) i :=
  install_slot slots4 (by decide) _ _ i
theorem bank4_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots4 j≠i) :
    bank4 C R root rank depth M mask i=bank3 C R root rank depth M mask i := install_other slots4 _ _ _ hi

theorem join4 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank3 C R root rank depth M mask (slots4 i)=(DimensionTemplate.input (2*C+3)) i := by
  intro i;fin_cases i
  · change bank3 C R root rank depth M mask 15=(DimensionTemplate.input (2*C+3)) 0
    rw [bank3_other C R root rank depth M mask 15 (by decide)]
    rw [bank2_other C R root rank depth M mask 15 (by decide)]
    change bank1 C R root rank depth M mask (slots1 9)=_
    rw [bank1_slot]
    simpa [UnaryAffine.input,DimensionTemplate.input] using affine_value C 2 3
  · change bank3 C R root rank depth M mask 29=(DimensionTemplate.input (2*C+3)) 1
    rw [bank3_other C R root rank depth M mask 29 (by decide)]
    rw [bank2_other C R root rank depth M mask 29 (by decide)]
    rw [bank1_other C R root rank depth M mask 29 (by decide)]
    rfl
  · change bank3 C R root rank depth M mask 30=(DimensionTemplate.input (2*C+3)) 2
    rw [bank3_other C R root rank depth M mask 30 (by decide)]
    rw [bank2_other C R root rank depth M mask 30 (by decide)]
    rw [bank1_other C R root rank depth M mask 30 (by decide)]
    rfl

theorem step4 (C R root rank depth M : Nat) (mask : List Bool) : Step phase4 (2*(2*C+3)+8)
    (fun _=>0) (bank3 C R root rank depth M mask) (fun _=>0) (bank4 C R root rank depth M mask) := by
  have focused:=(CycleCommonReserve.of_clock (DimensionTemplate.ready false (2*C+3))).focus slots4 (by decide) (fun _=>0) (bank3 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots4)
    (install_existing _ _ _ (join4 C R root rank depth M mask))).congr (zero_heads slots4) rfl
def joined4 := Composition.machine joined3 phase4
def budget4 (C R root rank depth M : Nat) (mask : List Bool) := budget3 C R root rank depth M mask+1+(2*(2*C+3)+8)
theorem run4 (C R root rank depth M : Nat) (mask : List Bool) : Step joined4 (budget4 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank4 C R root rank depth M mask) := (run3 C R root rank depth M mask).seq (step4 C R root rank depth M mask)

def slots5 : Fin 3→Fin 55 := ![1,31,32]
def phase5 := RecoveryFocus.machine slots5 (DimensionTemplate.machine false)
def bank5 (C R root rank depth M : Nat) (mask : List Bool) := install slots5 (bank4 C R root rank depth M mask) (DimensionTemplate.output false (R))
theorem bank5_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 3) :
    bank5 C R root rank depth M mask (slots5 i)=(DimensionTemplate.output false (R)) i :=
  install_slot slots5 (by decide) _ _ i
theorem bank5_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots5 j≠i) :
    bank5 C R root rank depth M mask i=bank4 C R root rank depth M mask i := install_other slots5 _ _ _ hi

theorem join5 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank4 C R root rank depth M mask (slots5 i)=(DimensionTemplate.input (R)) i := by
  intro i;fin_cases i
  · change bank4 C R root rank depth M mask 1=(DimensionTemplate.input (R)) 0
    rw [bank4_other C R root rank depth M mask 1 (by decide)]
    rw [bank3_other C R root rank depth M mask 1 (by decide)]
    rw [bank2_other C R root rank depth M mask 1 (by decide)]
    rw [bank1_other C R root rank depth M mask 1 (by decide)]
    rfl
  · change bank4 C R root rank depth M mask 31=(DimensionTemplate.input (R)) 1
    rw [bank4_other C R root rank depth M mask 31 (by decide)]
    rw [bank3_other C R root rank depth M mask 31 (by decide)]
    rw [bank2_other C R root rank depth M mask 31 (by decide)]
    rw [bank1_other C R root rank depth M mask 31 (by decide)]
    rfl
  · change bank4 C R root rank depth M mask 32=(DimensionTemplate.input (R)) 2
    rw [bank4_other C R root rank depth M mask 32 (by decide)]
    rw [bank3_other C R root rank depth M mask 32 (by decide)]
    rw [bank2_other C R root rank depth M mask 32 (by decide)]
    rw [bank1_other C R root rank depth M mask 32 (by decide)]
    rfl

theorem step5 (C R root rank depth M : Nat) (mask : List Bool) : Step phase5 (2*(R)+8)
    (fun _=>0) (bank4 C R root rank depth M mask) (fun _=>0) (bank5 C R root rank depth M mask) := by
  have focused:=(CycleCommonReserve.of_clock (DimensionTemplate.ready false (R))).focus slots5 (by decide) (fun _=>0) (bank4 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots5)
    (install_existing _ _ _ (join5 C R root rank depth M mask))).congr (zero_heads slots5) rfl
def joined5 := Composition.machine joined4 phase5
def budget5 (C R root rank depth M : Nat) (mask : List Bool) := budget4 C R root rank depth M mask+1+(2*(R)+8)
theorem run5 (C R root rank depth M : Nat) (mask : List Bool) : Step joined5 (budget5 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank5 C R root rank depth M mask) := (run4 C R root rank depth M mask).seq (step5 C R root rank depth M mask)

def slots6 : Fin 3→Fin 55 := ![3,33,34]
def phase6 := RecoveryFocus.machine slots6 (DimensionTemplate.machine false)
def bank6 (C R root rank depth M : Nat) (mask : List Bool) := install slots6 (bank5 C R root rank depth M mask) (DimensionTemplate.output false (rank))
theorem bank6_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 3) :
    bank6 C R root rank depth M mask (slots6 i)=(DimensionTemplate.output false (rank)) i :=
  install_slot slots6 (by decide) _ _ i
theorem bank6_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots6 j≠i) :
    bank6 C R root rank depth M mask i=bank5 C R root rank depth M mask i := install_other slots6 _ _ _ hi

theorem join6 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank5 C R root rank depth M mask (slots6 i)=(DimensionTemplate.input (rank)) i := by
  intro i;fin_cases i
  · change bank5 C R root rank depth M mask 3=(DimensionTemplate.input (rank)) 0
    rw [bank5_other C R root rank depth M mask 3 (by decide)]
    rw [bank4_other C R root rank depth M mask 3 (by decide)]
    rw [bank3_other C R root rank depth M mask 3 (by decide)]
    rw [bank2_other C R root rank depth M mask 3 (by decide)]
    rw [bank1_other C R root rank depth M mask 3 (by decide)]
    rfl
  · change bank5 C R root rank depth M mask 33=(DimensionTemplate.input (rank)) 1
    rw [bank5_other C R root rank depth M mask 33 (by decide)]
    rw [bank4_other C R root rank depth M mask 33 (by decide)]
    rw [bank3_other C R root rank depth M mask 33 (by decide)]
    rw [bank2_other C R root rank depth M mask 33 (by decide)]
    rw [bank1_other C R root rank depth M mask 33 (by decide)]
    rfl
  · change bank5 C R root rank depth M mask 34=(DimensionTemplate.input (rank)) 2
    rw [bank5_other C R root rank depth M mask 34 (by decide)]
    rw [bank4_other C R root rank depth M mask 34 (by decide)]
    rw [bank3_other C R root rank depth M mask 34 (by decide)]
    rw [bank2_other C R root rank depth M mask 34 (by decide)]
    rw [bank1_other C R root rank depth M mask 34 (by decide)]
    rfl

theorem step6 (C R root rank depth M : Nat) (mask : List Bool) : Step phase6 (2*(rank)+8)
    (fun _=>0) (bank5 C R root rank depth M mask) (fun _=>0) (bank6 C R root rank depth M mask) := by
  have focused:=(CycleCommonReserve.of_clock (DimensionTemplate.ready false (rank))).focus slots6 (by decide) (fun _=>0) (bank5 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots6)
    (install_existing _ _ _ (join6 C R root rank depth M mask))).congr (zero_heads slots6) rfl
def joined6 := Composition.machine joined5 phase6
def budget6 (C R root rank depth M : Nat) (mask : List Bool) := budget5 C R root rank depth M mask+1+(2*(rank)+8)
theorem run6 (C R root rank depth M : Nat) (mask : List Bool) : Step joined6 (budget6 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank6 C R root rank depth M mask) := (run5 C R root rank depth M mask).seq (step6 C R root rank depth M mask)

def slots7 : Fin 3→Fin 55 := ![4,35,36]
def phase7 := RecoveryFocus.machine slots7 (DimensionTemplate.machine false)
def bank7 (C R root rank depth M : Nat) (mask : List Bool) := install slots7 (bank6 C R root rank depth M mask) (DimensionTemplate.output false (depth))
theorem bank7_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 3) :
    bank7 C R root rank depth M mask (slots7 i)=(DimensionTemplate.output false (depth)) i :=
  install_slot slots7 (by decide) _ _ i
theorem bank7_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots7 j≠i) :
    bank7 C R root rank depth M mask i=bank6 C R root rank depth M mask i := install_other slots7 _ _ _ hi

theorem join7 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank6 C R root rank depth M mask (slots7 i)=(DimensionTemplate.input (depth)) i := by
  intro i;fin_cases i
  · change bank6 C R root rank depth M mask 4=(DimensionTemplate.input (depth)) 0
    rw [bank6_other C R root rank depth M mask 4 (by decide)]
    rw [bank5_other C R root rank depth M mask 4 (by decide)]
    rw [bank4_other C R root rank depth M mask 4 (by decide)]
    rw [bank3_other C R root rank depth M mask 4 (by decide)]
    rw [bank2_other C R root rank depth M mask 4 (by decide)]
    rw [bank1_other C R root rank depth M mask 4 (by decide)]
    rfl
  · change bank6 C R root rank depth M mask 35=(DimensionTemplate.input (depth)) 1
    rw [bank6_other C R root rank depth M mask 35 (by decide)]
    rw [bank5_other C R root rank depth M mask 35 (by decide)]
    rw [bank4_other C R root rank depth M mask 35 (by decide)]
    rw [bank3_other C R root rank depth M mask 35 (by decide)]
    rw [bank2_other C R root rank depth M mask 35 (by decide)]
    rw [bank1_other C R root rank depth M mask 35 (by decide)]
    rfl
  · change bank6 C R root rank depth M mask 36=(DimensionTemplate.input (depth)) 2
    rw [bank6_other C R root rank depth M mask 36 (by decide)]
    rw [bank5_other C R root rank depth M mask 36 (by decide)]
    rw [bank4_other C R root rank depth M mask 36 (by decide)]
    rw [bank3_other C R root rank depth M mask 36 (by decide)]
    rw [bank2_other C R root rank depth M mask 36 (by decide)]
    rw [bank1_other C R root rank depth M mask 36 (by decide)]
    rfl

theorem step7 (C R root rank depth M : Nat) (mask : List Bool) : Step phase7 (2*(depth)+8)
    (fun _=>0) (bank6 C R root rank depth M mask) (fun _=>0) (bank7 C R root rank depth M mask) := by
  have focused:=(CycleCommonReserve.of_clock (DimensionTemplate.ready false (depth))).focus slots7 (by decide) (fun _=>0) (bank6 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots7)
    (install_existing _ _ _ (join7 C R root rank depth M mask))).congr (zero_heads slots7) rfl
def joined7 := Composition.machine joined6 phase7
def budget7 (C R root rank depth M : Nat) (mask : List Bool) := budget6 C R root rank depth M mask+1+(2*(depth)+8)
theorem run7 (C R root rank depth M : Nat) (mask : List Bool) : Step joined7 (budget7 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank7 C R root rank depth M mask) := (run6 C R root rank depth M mask).seq (step7 C R root rank depth M mask)

def slots8 : Fin 3→Fin 55 := ![25,37,38]
def phase8 := RecoveryFocus.machine slots8 (DimensionTemplate.machine false)
def bank8 (C R root rank depth M : Nat) (mask : List Bool) := install slots8 (bank7 C R root rank depth M mask) (DimensionTemplate.output false (C+9))
theorem bank8_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 3) :
    bank8 C R root rank depth M mask (slots8 i)=(DimensionTemplate.output false (C+9)) i :=
  install_slot slots8 (by decide) _ _ i
theorem bank8_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots8 j≠i) :
    bank8 C R root rank depth M mask i=bank7 C R root rank depth M mask i := install_other slots8 _ _ _ hi

theorem join8 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank7 C R root rank depth M mask (slots8 i)=(DimensionTemplate.input (C+9)) i := by
  intro i;fin_cases i
  · change bank7 C R root rank depth M mask 25=(DimensionTemplate.input (C+9)) 0
    rw [bank7_other C R root rank depth M mask 25 (by decide)]
    rw [bank6_other C R root rank depth M mask 25 (by decide)]
    rw [bank5_other C R root rank depth M mask 25 (by decide)]
    rw [bank4_other C R root rank depth M mask 25 (by decide)]
    rw [bank3_other C R root rank depth M mask 25 (by decide)]
    change bank2 C R root rank depth M mask (slots2 9)=_
    rw [bank2_slot]
    simpa [UnaryAffine.input,DimensionTemplate.input] using affine_value C 1 9
  · change bank7 C R root rank depth M mask 37=(DimensionTemplate.input (C+9)) 1
    rw [bank7_other C R root rank depth M mask 37 (by decide)]
    rw [bank6_other C R root rank depth M mask 37 (by decide)]
    rw [bank5_other C R root rank depth M mask 37 (by decide)]
    rw [bank4_other C R root rank depth M mask 37 (by decide)]
    rw [bank3_other C R root rank depth M mask 37 (by decide)]
    rw [bank2_other C R root rank depth M mask 37 (by decide)]
    rw [bank1_other C R root rank depth M mask 37 (by decide)]
    rfl
  · change bank7 C R root rank depth M mask 38=(DimensionTemplate.input (C+9)) 2
    rw [bank7_other C R root rank depth M mask 38 (by decide)]
    rw [bank6_other C R root rank depth M mask 38 (by decide)]
    rw [bank5_other C R root rank depth M mask 38 (by decide)]
    rw [bank4_other C R root rank depth M mask 38 (by decide)]
    rw [bank3_other C R root rank depth M mask 38 (by decide)]
    rw [bank2_other C R root rank depth M mask 38 (by decide)]
    rw [bank1_other C R root rank depth M mask 38 (by decide)]
    rfl

theorem step8 (C R root rank depth M : Nat) (mask : List Bool) : Step phase8 (2*(C+9)+8)
    (fun _=>0) (bank7 C R root rank depth M mask) (fun _=>0) (bank8 C R root rank depth M mask) := by
  have focused:=(CycleCommonReserve.of_clock (DimensionTemplate.ready false (C+9))).focus slots8 (by decide) (fun _=>0) (bank7 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots8)
    (install_existing _ _ _ (join8 C R root rank depth M mask))).congr (zero_heads slots8) rfl
def joined8 := Composition.machine joined7 phase8
def budget8 (C R root rank depth M : Nat) (mask : List Bool) := budget7 C R root rank depth M mask+1+(2*(C+9)+8)
theorem run8 (C R root rank depth M : Nat) (mask : List Bool) : Step joined8 (budget8 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank8 C R root rank depth M mask) := (run7 C R root rank depth M mask).seq (step8 C R root rank depth M mask)

def slots9 : Fin 3→Fin 55 := ![5,39,40]
def phase9 := RecoveryFocus.machine slots9 (DimensionTemplate.machine false)
def bank9 (C R root rank depth M : Nat) (mask : List Bool) := install slots9 (bank8 C R root rank depth M mask) (DimensionTemplate.output false (M))
theorem bank9_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 3) :
    bank9 C R root rank depth M mask (slots9 i)=(DimensionTemplate.output false (M)) i :=
  install_slot slots9 (by decide) _ _ i
theorem bank9_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots9 j≠i) :
    bank9 C R root rank depth M mask i=bank8 C R root rank depth M mask i := install_other slots9 _ _ _ hi

theorem join9 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank8 C R root rank depth M mask (slots9 i)=(DimensionTemplate.input (M)) i := by
  intro i;fin_cases i
  · change bank8 C R root rank depth M mask 5=(DimensionTemplate.input (M)) 0
    rw [bank8_other C R root rank depth M mask 5 (by decide)]
    rw [bank7_other C R root rank depth M mask 5 (by decide)]
    rw [bank6_other C R root rank depth M mask 5 (by decide)]
    rw [bank5_other C R root rank depth M mask 5 (by decide)]
    rw [bank4_other C R root rank depth M mask 5 (by decide)]
    rw [bank3_other C R root rank depth M mask 5 (by decide)]
    rw [bank2_other C R root rank depth M mask 5 (by decide)]
    rw [bank1_other C R root rank depth M mask 5 (by decide)]
    rfl
  · change bank8 C R root rank depth M mask 39=(DimensionTemplate.input (M)) 1
    rw [bank8_other C R root rank depth M mask 39 (by decide)]
    rw [bank7_other C R root rank depth M mask 39 (by decide)]
    rw [bank6_other C R root rank depth M mask 39 (by decide)]
    rw [bank5_other C R root rank depth M mask 39 (by decide)]
    rw [bank4_other C R root rank depth M mask 39 (by decide)]
    rw [bank3_other C R root rank depth M mask 39 (by decide)]
    rw [bank2_other C R root rank depth M mask 39 (by decide)]
    rw [bank1_other C R root rank depth M mask 39 (by decide)]
    rfl
  · change bank8 C R root rank depth M mask 40=(DimensionTemplate.input (M)) 2
    rw [bank8_other C R root rank depth M mask 40 (by decide)]
    rw [bank7_other C R root rank depth M mask 40 (by decide)]
    rw [bank6_other C R root rank depth M mask 40 (by decide)]
    rw [bank5_other C R root rank depth M mask 40 (by decide)]
    rw [bank4_other C R root rank depth M mask 40 (by decide)]
    rw [bank3_other C R root rank depth M mask 40 (by decide)]
    rw [bank2_other C R root rank depth M mask 40 (by decide)]
    rw [bank1_other C R root rank depth M mask 40 (by decide)]
    rfl

theorem step9 (C R root rank depth M : Nat) (mask : List Bool) : Step phase9 (2*(M)+8)
    (fun _=>0) (bank8 C R root rank depth M mask) (fun _=>0) (bank9 C R root rank depth M mask) := by
  have focused:=(CycleCommonReserve.of_clock (DimensionTemplate.ready false (M))).focus slots9 (by decide) (fun _=>0) (bank8 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots9)
    (install_existing _ _ _ (join9 C R root rank depth M mask))).congr (zero_heads slots9) rfl
def joined9 := Composition.machine joined8 phase9
def budget9 (C R root rank depth M : Nat) (mask : List Bool) := budget8 C R root rank depth M mask+1+(2*(M)+8)
theorem run9 (C R root rank depth M : Nat) (mask : List Bool) : Step joined9 (budget9 C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank9 C R root rank depth M mask) := (run8 C R root rank depth M mask).seq (step9 C R root rank depth M mask)
end
end Theorem25Completion.WalkLiteralMasters
