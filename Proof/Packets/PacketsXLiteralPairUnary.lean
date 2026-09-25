import Proof.CaseAnalysis.RowsCountBinary
import Proof.Packets.PacketsXLiteralPair

/-! Paid unary metadata to exact native literal-pair cache record. No binary
index, normalized pair operand, or completed result is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairUnary
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.RepairOrdinary.SignedSortKey
noncomputable section

theorem of_clock {t st n : Nat} {p : Machine t st} {A B : Fin t→List Bool}
    (h : ClockJoin.ReadyRun p n A B) : Step p n (fun _=>0) A (fun _=>0) B := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,funext hh,ht,hs⟩

def input1 (R tag _index : Nat) := UWalkUnary.input R tag
def output1 (R tag _index : Nat) := UWalkUnary.result false false R tag
def worker1 := UWalkUnary.machine false false
def cost1 (_R tag _index : Nat) := 2*tag+6
theorem local1 (R tag index : Nat) : Step worker1 (cost1 R tag index)
    (fun _=>0) (input1 R tag index) (fun _=>0) (output1 R tag index) :=
  of_clock (UWalkUnary.ready false false R tag)

def input2 (_R tag _index : Nat) := CloseoutRowsCountBinary.input tag
def output2 (_R tag _index : Nat) := Classical.choose (CloseoutRowsCountBinary.count_run tag)
def worker2 := CloseoutRowsCountBinary.machine
def cost2 (_R tag _index : Nat) := CloseoutRowsCountBinary.budget tag
theorem local2 (R tag index : Nat) : Step worker2 (cost2 R tag index)
    (fun _=>0) (input2 R tag index) (fun _=>0) (output2 R tag index) :=
  of_clock (Classical.choose_spec (CloseoutRowsCountBinary.count_run tag)).1
theorem binary2 (R tag index : Nat) : output2 R tag index 5=
    frame (CloseoutRowsCountBinary.bits tag) :=
  (Classical.choose_spec (CloseoutRowsCountBinary.count_run tag)).2.2.2

def input3 (R _tag index : Nat) := UWalkUnary.input R index
def output3 (R _tag index : Nat) := UWalkUnary.result false false R index
def worker3 := UWalkUnary.machine false false
def cost3 (_R _tag index : Nat) := 2*index+6
theorem local3 (R tag index : Nat) : Step worker3 (cost3 R tag index)
    (fun _=>0) (input3 R tag index) (fun _=>0) (output3 R tag index) :=
  of_clock (UWalkUnary.ready false false R index)

def input4 (_R _tag index : Nat) := CloseoutRowsCountBinary.input index
def output4 (_R _tag index : Nat) := Classical.choose (CloseoutRowsCountBinary.count_run index)
def worker4 := CloseoutRowsCountBinary.machine
def cost4 (_R _tag index : Nat) := CloseoutRowsCountBinary.budget index
theorem local4 (R tag index : Nat) : Step worker4 (cost4 R tag index)
    (fun _=>0) (input4 R tag index) (fun _=>0) (output4 R tag index) :=
  of_clock (Classical.choose_spec (CloseoutRowsCountBinary.count_run index)).1
theorem binary4 (R tag index : Nat) : output4 R tag index 5=
    frame (CloseoutRowsCountBinary.bits index) :=
  (Classical.choose_spec (CloseoutRowsCountBinary.count_run index)).2.2.2

def input5 (_R tag index : Nat) (pre : List Bool) :=
  LiteralPairCold.input (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index) pre
def output5 (_R tag index : Nat) (pre : List Bool) := Classical.choose
  (LiteralPairCold.run (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index) pre)
def worker5 := LiteralPairCold.machine
def cost5 (_R tag index : Nat) :=
  LiteralPairCold.budget (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index)
def next (tag index : Nat) (pre : List Bool) := pre++ReflectedLiteralCache.singletonWord (Nat.pair tag index)
theorem local5 (R tag index : Nat) (pre : List Bool) : Step worker5 (cost5 R tag index)
    (LiteralPairCold.heads pre) (input5 R tag index pre)
    (LiteralPairCold.heads (next tag index pre)) (output5 R tag index pre) := by
  have h := (Classical.choose_spec
    (LiteralPairCold.run (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index) pre)).1
  apply h.congr _ rfl
  simp only [CloseoutRowsCountBinary.value_bits]
  rfl
theorem value5 (R tag index : Nat) (pre : List Bool) : output5 R tag index pre 35=next tag index pre := by
  have h := (Classical.choose_spec
    (LiteralPairCold.run (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index) pre)).2
  apply h.trans
  simp only [CloseoutRowsCountBinary.value_bits]
  rfl

def heads (pre : List Bool) (i : Fin 58) : Nat := if i=2 then pre.length else 0
def input (R tag index : Nat) (pre : List Bool) (i : Fin 58) : List Bool :=
  if i=0 then UWalkUnary.source R tag else if i=1 then UWalkUnary.source R index
  else if i=2 then pre else []
-- BEGIN GENERATED WIRING

def slots1 : Fin 3→Fin 58 := ![0,3,4]
theorem injective1 : Function.Injective slots1 := by decide
def phase1 := RecoveryFocus.machine slots1 worker1
def bank1 (R tag index : Nat) (pre : List Bool) := install slots1 (input R tag index pre) (output1 R tag index)
theorem bank1_slot (R tag index : Nat) (pre : List Bool) (j : Fin 3) :
    bank1 R tag index pre (slots1 j)=output1 R tag index j := install_slot slots1 injective1 _ _ j
theorem bank1_other (R tag index : Nat) (pre : List Bool) (i : Fin 58)
    (hi : ∀ j,slots1 j≠i) : bank1 R tag index pre i=input R tag index pre i := install_other slots1 _ _ _ hi

theorem input1_join (R tag index : Nat) (pre : List Bool) :
    ∀ j,input R tag index pre (slots1 j)=input1 R tag index j := by
  intro j
  fin_cases j
  · change input R tag index pre 0=input1 R tag index 0
    rfl
  · change input R tag index pre 3=input1 R tag index 1
    rfl
  · change input R tag index pre 4=input1 R tag index 2
    rfl
theorem step1 (R tag index : Nat) (pre : List Bool) :
    Step phase1 (cost1 R tag index) (heads pre) (input R tag index pre)
      (heads pre) (bank1 R tag index pre) := by
  apply PhysicalFocusBoundary.focus (local1 R tag index) slots1 injective1
    (heads pre) (heads pre) (input R tag index pre) (bank1 R tag index pre)
  · intro j;fin_cases j <;>rfl
  · intro j;exact (input1_join R tag index pre j).symm
  · intro j;fin_cases j <;>rfl
  · intro j;exact (bank1_slot R tag index pre j).symm
  · intro i hi
    refine ⟨?_,(bank1_other R tag index pre i hi).symm⟩
    rfl
def joined1 := phase1
def budget1 (R tag index : Nat) := cost1 R tag index
theorem run1 (R tag index : Nat) (pre : List Bool) : Step joined1 (budget1 R tag index)
    (heads pre) (input R tag index pre) (heads pre) (bank1 R tag index pre) := step1 R tag index pre

def slots2 : Fin 10→Fin 58 := ![3,5,6,7,8,9,10,11,12,13]
theorem injective2 : Function.Injective slots2 := by decide
def phase2 := RecoveryFocus.machine slots2 worker2
def bank2 (R tag index : Nat) (pre : List Bool) := install slots2 (bank1 R tag index pre) (output2 R tag index)
theorem bank2_slot (R tag index : Nat) (pre : List Bool) (j : Fin 10) :
    bank2 R tag index pre (slots2 j)=output2 R tag index j := install_slot slots2 injective2 _ _ j
theorem bank2_other (R tag index : Nat) (pre : List Bool) (i : Fin 58)
    (hi : ∀ j,slots2 j≠i) : bank2 R tag index pre i=bank1 R tag index pre i := install_other slots2 _ _ _ hi

theorem input2_join (R tag index : Nat) (pre : List Bool) :
    ∀ j,bank1 R tag index pre (slots2 j)=input2 R tag index j := by
  intro j
  fin_cases j
  · change bank1 R tag index pre 3=input2 R tag index 0
    change bank1 R tag index pre (slots1 1)=_
    rw [bank1_slot]
    rfl
  · change bank1 R tag index pre 5=input2 R tag index 1
    rw [bank1_other R tag index pre 5 (by decide)]
    rfl
  · change bank1 R tag index pre 6=input2 R tag index 2
    rw [bank1_other R tag index pre 6 (by decide)]
    rfl
  · change bank1 R tag index pre 7=input2 R tag index 3
    rw [bank1_other R tag index pre 7 (by decide)]
    rfl
  · change bank1 R tag index pre 8=input2 R tag index 4
    rw [bank1_other R tag index pre 8 (by decide)]
    rfl
  · change bank1 R tag index pre 9=input2 R tag index 5
    rw [bank1_other R tag index pre 9 (by decide)]
    rfl
  · change bank1 R tag index pre 10=input2 R tag index 6
    rw [bank1_other R tag index pre 10 (by decide)]
    rfl
  · change bank1 R tag index pre 11=input2 R tag index 7
    rw [bank1_other R tag index pre 11 (by decide)]
    rfl
  · change bank1 R tag index pre 12=input2 R tag index 8
    rw [bank1_other R tag index pre 12 (by decide)]
    rfl
  · change bank1 R tag index pre 13=input2 R tag index 9
    rw [bank1_other R tag index pre 13 (by decide)]
    rfl
theorem step2 (R tag index : Nat) (pre : List Bool) :
    Step phase2 (cost2 R tag index) (heads pre) (bank1 R tag index pre)
      (heads pre) (bank2 R tag index pre) := by
  apply PhysicalFocusBoundary.focus (local2 R tag index) slots2 injective2
    (heads pre) (heads pre) (bank1 R tag index pre) (bank2 R tag index pre)
  · intro j;fin_cases j <;>rfl
  · intro j;exact (input2_join R tag index pre j).symm
  · intro j;fin_cases j <;>rfl
  · intro j;exact (bank2_slot R tag index pre j).symm
  · intro i hi
    refine ⟨?_,(bank2_other R tag index pre i hi).symm⟩
    rfl
def joined2 := Composition.machine joined1 phase2
def budget2 (R tag index : Nat) := budget1 R tag index+1+cost2 R tag index
theorem run2 (R tag index : Nat) (pre : List Bool) : Step joined2 (budget2 R tag index)
    (heads pre) (input R tag index pre) (heads pre) (bank2 R tag index pre) :=
  (run1 R tag index pre).seq (step2 R tag index pre)

def slots3 : Fin 3→Fin 58 := ![1,14,15]
theorem injective3 : Function.Injective slots3 := by decide
def phase3 := RecoveryFocus.machine slots3 worker3
def bank3 (R tag index : Nat) (pre : List Bool) := install slots3 (bank2 R tag index pre) (output3 R tag index)
theorem bank3_slot (R tag index : Nat) (pre : List Bool) (j : Fin 3) :
    bank3 R tag index pre (slots3 j)=output3 R tag index j := install_slot slots3 injective3 _ _ j
theorem bank3_other (R tag index : Nat) (pre : List Bool) (i : Fin 58)
    (hi : ∀ j,slots3 j≠i) : bank3 R tag index pre i=bank2 R tag index pre i := install_other slots3 _ _ _ hi

theorem input3_join (R tag index : Nat) (pre : List Bool) :
    ∀ j,bank2 R tag index pre (slots3 j)=input3 R tag index j := by
  intro j
  fin_cases j
  · change bank2 R tag index pre 1=input3 R tag index 0
    rw [bank2_other R tag index pre 1 (by decide)]
    rw [bank1_other R tag index pre 1 (by decide)]
    rfl
  · change bank2 R tag index pre 14=input3 R tag index 1
    rw [bank2_other R tag index pre 14 (by decide)]
    rw [bank1_other R tag index pre 14 (by decide)]
    rfl
  · change bank2 R tag index pre 15=input3 R tag index 2
    rw [bank2_other R tag index pre 15 (by decide)]
    rw [bank1_other R tag index pre 15 (by decide)]
    rfl
theorem step3 (R tag index : Nat) (pre : List Bool) :
    Step phase3 (cost3 R tag index) (heads pre) (bank2 R tag index pre)
      (heads pre) (bank3 R tag index pre) := by
  apply PhysicalFocusBoundary.focus (local3 R tag index) slots3 injective3
    (heads pre) (heads pre) (bank2 R tag index pre) (bank3 R tag index pre)
  · intro j;fin_cases j <;>rfl
  · intro j;exact (input3_join R tag index pre j).symm
  · intro j;fin_cases j <;>rfl
  · intro j;exact (bank3_slot R tag index pre j).symm
  · intro i hi
    refine ⟨?_,(bank3_other R tag index pre i hi).symm⟩
    rfl
def joined3 := Composition.machine joined2 phase3
def budget3 (R tag index : Nat) := budget2 R tag index+1+cost3 R tag index
theorem run3 (R tag index : Nat) (pre : List Bool) : Step joined3 (budget3 R tag index)
    (heads pre) (input R tag index pre) (heads pre) (bank3 R tag index pre) :=
  (run2 R tag index pre).seq (step3 R tag index pre)

def slots4 : Fin 10→Fin 58 := ![14,16,17,18,19,20,21,22,23,24]
theorem injective4 : Function.Injective slots4 := by decide
def phase4 := RecoveryFocus.machine slots4 worker4
def bank4 (R tag index : Nat) (pre : List Bool) := install slots4 (bank3 R tag index pre) (output4 R tag index)
theorem bank4_slot (R tag index : Nat) (pre : List Bool) (j : Fin 10) :
    bank4 R tag index pre (slots4 j)=output4 R tag index j := install_slot slots4 injective4 _ _ j
theorem bank4_other (R tag index : Nat) (pre : List Bool) (i : Fin 58)
    (hi : ∀ j,slots4 j≠i) : bank4 R tag index pre i=bank3 R tag index pre i := install_other slots4 _ _ _ hi

theorem input4_join (R tag index : Nat) (pre : List Bool) :
    ∀ j,bank3 R tag index pre (slots4 j)=input4 R tag index j := by
  intro j
  fin_cases j
  · change bank3 R tag index pre 14=input4 R tag index 0
    change bank3 R tag index pre (slots3 1)=_
    rw [bank3_slot]
    rfl
  · change bank3 R tag index pre 16=input4 R tag index 1
    rw [bank3_other R tag index pre 16 (by decide)]
    rw [bank2_other R tag index pre 16 (by decide)]
    rw [bank1_other R tag index pre 16 (by decide)]
    rfl
  · change bank3 R tag index pre 17=input4 R tag index 2
    rw [bank3_other R tag index pre 17 (by decide)]
    rw [bank2_other R tag index pre 17 (by decide)]
    rw [bank1_other R tag index pre 17 (by decide)]
    rfl
  · change bank3 R tag index pre 18=input4 R tag index 3
    rw [bank3_other R tag index pre 18 (by decide)]
    rw [bank2_other R tag index pre 18 (by decide)]
    rw [bank1_other R tag index pre 18 (by decide)]
    rfl
  · change bank3 R tag index pre 19=input4 R tag index 4
    rw [bank3_other R tag index pre 19 (by decide)]
    rw [bank2_other R tag index pre 19 (by decide)]
    rw [bank1_other R tag index pre 19 (by decide)]
    rfl
  · change bank3 R tag index pre 20=input4 R tag index 5
    rw [bank3_other R tag index pre 20 (by decide)]
    rw [bank2_other R tag index pre 20 (by decide)]
    rw [bank1_other R tag index pre 20 (by decide)]
    rfl
  · change bank3 R tag index pre 21=input4 R tag index 6
    rw [bank3_other R tag index pre 21 (by decide)]
    rw [bank2_other R tag index pre 21 (by decide)]
    rw [bank1_other R tag index pre 21 (by decide)]
    rfl
  · change bank3 R tag index pre 22=input4 R tag index 7
    rw [bank3_other R tag index pre 22 (by decide)]
    rw [bank2_other R tag index pre 22 (by decide)]
    rw [bank1_other R tag index pre 22 (by decide)]
    rfl
  · change bank3 R tag index pre 23=input4 R tag index 8
    rw [bank3_other R tag index pre 23 (by decide)]
    rw [bank2_other R tag index pre 23 (by decide)]
    rw [bank1_other R tag index pre 23 (by decide)]
    rfl
  · change bank3 R tag index pre 24=input4 R tag index 9
    rw [bank3_other R tag index pre 24 (by decide)]
    rw [bank2_other R tag index pre 24 (by decide)]
    rw [bank1_other R tag index pre 24 (by decide)]
    rfl
theorem step4 (R tag index : Nat) (pre : List Bool) :
    Step phase4 (cost4 R tag index) (heads pre) (bank3 R tag index pre)
      (heads pre) (bank4 R tag index pre) := by
  apply PhysicalFocusBoundary.focus (local4 R tag index) slots4 injective4
    (heads pre) (heads pre) (bank3 R tag index pre) (bank4 R tag index pre)
  · intro j;fin_cases j <;>rfl
  · intro j;exact (input4_join R tag index pre j).symm
  · intro j;fin_cases j <;>rfl
  · intro j;exact (bank4_slot R tag index pre j).symm
  · intro i hi
    refine ⟨?_,(bank4_other R tag index pre i hi).symm⟩
    rfl
def joined4 := Composition.machine joined3 phase4
def budget4 (R tag index : Nat) := budget3 R tag index+1+cost4 R tag index
theorem run4 (R tag index : Nat) (pre : List Bool) : Step joined4 (budget4 R tag index)
    (heads pre) (input R tag index pre) (heads pre) (bank4 R tag index pre) :=
  (run3 R tag index pre).seq (step4 R tag index pre)

def slots5 : Fin 36→Fin 58 := ![25,26,9,20,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,2]
theorem injective5 : Function.Injective slots5 := by decide
def phase5 := RecoveryFocus.machine slots5 worker5
def bank5 (R tag index : Nat) (pre : List Bool) := install slots5 (bank4 R tag index pre) (output5 R tag index pre)
theorem bank5_slot (R tag index : Nat) (pre : List Bool) (j : Fin 36) :
    bank5 R tag index pre (slots5 j)=output5 R tag index pre j := install_slot slots5 injective5 _ _ j
theorem bank5_other (R tag index : Nat) (pre : List Bool) (i : Fin 58)
    (hi : ∀ j,slots5 j≠i) : bank5 R tag index pre i=bank4 R tag index pre i := install_other slots5 _ _ _ hi

theorem input5_join (R tag index : Nat) (pre : List Bool) :
    ∀ j,bank4 R tag index pre (slots5 j)=input5 R tag index pre j := by
  intro j
  fin_cases j
  · change bank4 R tag index pre 25=input5 R tag index pre 0
    rw [bank4_other R tag index pre 25 (by decide)]
    rw [bank3_other R tag index pre 25 (by decide)]
    rw [bank2_other R tag index pre 25 (by decide)]
    rw [bank1_other R tag index pre 25 (by decide)]
    rfl
  · change bank4 R tag index pre 26=input5 R tag index pre 1
    rw [bank4_other R tag index pre 26 (by decide)]
    rw [bank3_other R tag index pre 26 (by decide)]
    rw [bank2_other R tag index pre 26 (by decide)]
    rw [bank1_other R tag index pre 26 (by decide)]
    rfl
  · change bank4 R tag index pre 9=input5 R tag index pre 2
    rw [bank4_other R tag index pre 9 (by decide)]
    rw [bank3_other R tag index pre 9 (by decide)]
    change bank2 R tag index pre (slots2 5)=_
    rw [bank2_slot]
    exact binary2 R tag index
  · change bank4 R tag index pre 20=input5 R tag index pre 3
    change bank4 R tag index pre (slots4 5)=_
    rw [bank4_slot]
    exact binary4 R tag index
  · change bank4 R tag index pre 27=input5 R tag index pre 4
    rw [bank4_other R tag index pre 27 (by decide)]
    rw [bank3_other R tag index pre 27 (by decide)]
    rw [bank2_other R tag index pre 27 (by decide)]
    rw [bank1_other R tag index pre 27 (by decide)]
    rfl
  · change bank4 R tag index pre 28=input5 R tag index pre 5
    rw [bank4_other R tag index pre 28 (by decide)]
    rw [bank3_other R tag index pre 28 (by decide)]
    rw [bank2_other R tag index pre 28 (by decide)]
    rw [bank1_other R tag index pre 28 (by decide)]
    rfl
  · change bank4 R tag index pre 29=input5 R tag index pre 6
    rw [bank4_other R tag index pre 29 (by decide)]
    rw [bank3_other R tag index pre 29 (by decide)]
    rw [bank2_other R tag index pre 29 (by decide)]
    rw [bank1_other R tag index pre 29 (by decide)]
    rfl
  · change bank4 R tag index pre 30=input5 R tag index pre 7
    rw [bank4_other R tag index pre 30 (by decide)]
    rw [bank3_other R tag index pre 30 (by decide)]
    rw [bank2_other R tag index pre 30 (by decide)]
    rw [bank1_other R tag index pre 30 (by decide)]
    rfl
  · change bank4 R tag index pre 31=input5 R tag index pre 8
    rw [bank4_other R tag index pre 31 (by decide)]
    rw [bank3_other R tag index pre 31 (by decide)]
    rw [bank2_other R tag index pre 31 (by decide)]
    rw [bank1_other R tag index pre 31 (by decide)]
    rfl
  · change bank4 R tag index pre 32=input5 R tag index pre 9
    rw [bank4_other R tag index pre 32 (by decide)]
    rw [bank3_other R tag index pre 32 (by decide)]
    rw [bank2_other R tag index pre 32 (by decide)]
    rw [bank1_other R tag index pre 32 (by decide)]
    rfl
  · change bank4 R tag index pre 33=input5 R tag index pre 10
    rw [bank4_other R tag index pre 33 (by decide)]
    rw [bank3_other R tag index pre 33 (by decide)]
    rw [bank2_other R tag index pre 33 (by decide)]
    rw [bank1_other R tag index pre 33 (by decide)]
    rfl
  · change bank4 R tag index pre 34=input5 R tag index pre 11
    rw [bank4_other R tag index pre 34 (by decide)]
    rw [bank3_other R tag index pre 34 (by decide)]
    rw [bank2_other R tag index pre 34 (by decide)]
    rw [bank1_other R tag index pre 34 (by decide)]
    rfl
  · change bank4 R tag index pre 35=input5 R tag index pre 12
    rw [bank4_other R tag index pre 35 (by decide)]
    rw [bank3_other R tag index pre 35 (by decide)]
    rw [bank2_other R tag index pre 35 (by decide)]
    rw [bank1_other R tag index pre 35 (by decide)]
    rfl
  · change bank4 R tag index pre 36=input5 R tag index pre 13
    rw [bank4_other R tag index pre 36 (by decide)]
    rw [bank3_other R tag index pre 36 (by decide)]
    rw [bank2_other R tag index pre 36 (by decide)]
    rw [bank1_other R tag index pre 36 (by decide)]
    rfl
  · change bank4 R tag index pre 37=input5 R tag index pre 14
    rw [bank4_other R tag index pre 37 (by decide)]
    rw [bank3_other R tag index pre 37 (by decide)]
    rw [bank2_other R tag index pre 37 (by decide)]
    rw [bank1_other R tag index pre 37 (by decide)]
    rfl
  · change bank4 R tag index pre 38=input5 R tag index pre 15
    rw [bank4_other R tag index pre 38 (by decide)]
    rw [bank3_other R tag index pre 38 (by decide)]
    rw [bank2_other R tag index pre 38 (by decide)]
    rw [bank1_other R tag index pre 38 (by decide)]
    rfl
  · change bank4 R tag index pre 39=input5 R tag index pre 16
    rw [bank4_other R tag index pre 39 (by decide)]
    rw [bank3_other R tag index pre 39 (by decide)]
    rw [bank2_other R tag index pre 39 (by decide)]
    rw [bank1_other R tag index pre 39 (by decide)]
    rfl
  · change bank4 R tag index pre 40=input5 R tag index pre 17
    rw [bank4_other R tag index pre 40 (by decide)]
    rw [bank3_other R tag index pre 40 (by decide)]
    rw [bank2_other R tag index pre 40 (by decide)]
    rw [bank1_other R tag index pre 40 (by decide)]
    rfl
  · change bank4 R tag index pre 41=input5 R tag index pre 18
    rw [bank4_other R tag index pre 41 (by decide)]
    rw [bank3_other R tag index pre 41 (by decide)]
    rw [bank2_other R tag index pre 41 (by decide)]
    rw [bank1_other R tag index pre 41 (by decide)]
    rfl
  · change bank4 R tag index pre 42=input5 R tag index pre 19
    rw [bank4_other R tag index pre 42 (by decide)]
    rw [bank3_other R tag index pre 42 (by decide)]
    rw [bank2_other R tag index pre 42 (by decide)]
    rw [bank1_other R tag index pre 42 (by decide)]
    rfl
  · change bank4 R tag index pre 43=input5 R tag index pre 20
    rw [bank4_other R tag index pre 43 (by decide)]
    rw [bank3_other R tag index pre 43 (by decide)]
    rw [bank2_other R tag index pre 43 (by decide)]
    rw [bank1_other R tag index pre 43 (by decide)]
    rfl
  · change bank4 R tag index pre 44=input5 R tag index pre 21
    rw [bank4_other R tag index pre 44 (by decide)]
    rw [bank3_other R tag index pre 44 (by decide)]
    rw [bank2_other R tag index pre 44 (by decide)]
    rw [bank1_other R tag index pre 44 (by decide)]
    rfl
  · change bank4 R tag index pre 45=input5 R tag index pre 22
    rw [bank4_other R tag index pre 45 (by decide)]
    rw [bank3_other R tag index pre 45 (by decide)]
    rw [bank2_other R tag index pre 45 (by decide)]
    rw [bank1_other R tag index pre 45 (by decide)]
    rfl
  · change bank4 R tag index pre 46=input5 R tag index pre 23
    rw [bank4_other R tag index pre 46 (by decide)]
    rw [bank3_other R tag index pre 46 (by decide)]
    rw [bank2_other R tag index pre 46 (by decide)]
    rw [bank1_other R tag index pre 46 (by decide)]
    rfl
  · change bank4 R tag index pre 47=input5 R tag index pre 24
    rw [bank4_other R tag index pre 47 (by decide)]
    rw [bank3_other R tag index pre 47 (by decide)]
    rw [bank2_other R tag index pre 47 (by decide)]
    rw [bank1_other R tag index pre 47 (by decide)]
    rfl
  · change bank4 R tag index pre 48=input5 R tag index pre 25
    rw [bank4_other R tag index pre 48 (by decide)]
    rw [bank3_other R tag index pre 48 (by decide)]
    rw [bank2_other R tag index pre 48 (by decide)]
    rw [bank1_other R tag index pre 48 (by decide)]
    rfl
  · change bank4 R tag index pre 49=input5 R tag index pre 26
    rw [bank4_other R tag index pre 49 (by decide)]
    rw [bank3_other R tag index pre 49 (by decide)]
    rw [bank2_other R tag index pre 49 (by decide)]
    rw [bank1_other R tag index pre 49 (by decide)]
    rfl
  · change bank4 R tag index pre 50=input5 R tag index pre 27
    rw [bank4_other R tag index pre 50 (by decide)]
    rw [bank3_other R tag index pre 50 (by decide)]
    rw [bank2_other R tag index pre 50 (by decide)]
    rw [bank1_other R tag index pre 50 (by decide)]
    rfl
  · change bank4 R tag index pre 51=input5 R tag index pre 28
    rw [bank4_other R tag index pre 51 (by decide)]
    rw [bank3_other R tag index pre 51 (by decide)]
    rw [bank2_other R tag index pre 51 (by decide)]
    rw [bank1_other R tag index pre 51 (by decide)]
    rfl
  · change bank4 R tag index pre 52=input5 R tag index pre 29
    rw [bank4_other R tag index pre 52 (by decide)]
    rw [bank3_other R tag index pre 52 (by decide)]
    rw [bank2_other R tag index pre 52 (by decide)]
    rw [bank1_other R tag index pre 52 (by decide)]
    rfl
  · change bank4 R tag index pre 53=input5 R tag index pre 30
    rw [bank4_other R tag index pre 53 (by decide)]
    rw [bank3_other R tag index pre 53 (by decide)]
    rw [bank2_other R tag index pre 53 (by decide)]
    rw [bank1_other R tag index pre 53 (by decide)]
    rfl
  · change bank4 R tag index pre 54=input5 R tag index pre 31
    rw [bank4_other R tag index pre 54 (by decide)]
    rw [bank3_other R tag index pre 54 (by decide)]
    rw [bank2_other R tag index pre 54 (by decide)]
    rw [bank1_other R tag index pre 54 (by decide)]
    rfl
  · change bank4 R tag index pre 55=input5 R tag index pre 32
    rw [bank4_other R tag index pre 55 (by decide)]
    rw [bank3_other R tag index pre 55 (by decide)]
    rw [bank2_other R tag index pre 55 (by decide)]
    rw [bank1_other R tag index pre 55 (by decide)]
    rfl
  · change bank4 R tag index pre 56=input5 R tag index pre 33
    rw [bank4_other R tag index pre 56 (by decide)]
    rw [bank3_other R tag index pre 56 (by decide)]
    rw [bank2_other R tag index pre 56 (by decide)]
    rw [bank1_other R tag index pre 56 (by decide)]
    rfl
  · change bank4 R tag index pre 57=input5 R tag index pre 34
    rw [bank4_other R tag index pre 57 (by decide)]
    rw [bank3_other R tag index pre 57 (by decide)]
    rw [bank2_other R tag index pre 57 (by decide)]
    rw [bank1_other R tag index pre 57 (by decide)]
    rfl
  · change bank4 R tag index pre 2=input5 R tag index pre 35
    rw [bank4_other R tag index pre 2 (by decide)]
    rw [bank3_other R tag index pre 2 (by decide)]
    rw [bank2_other R tag index pre 2 (by decide)]
    rw [bank1_other R tag index pre 2 (by decide)]
    rfl
theorem step5 (R tag index : Nat) (pre : List Bool) :
    Step phase5 (cost5 R tag index) (heads pre) (bank4 R tag index pre)
      (heads (next tag index pre)) (bank5 R tag index pre) := by
  apply PhysicalFocusBoundary.focus (local5 R tag index pre) slots5 injective5
    (heads pre) (heads (next tag index pre)) (bank4 R tag index pre) (bank5 R tag index pre)
  · intro j;fin_cases j <;>rfl
  · intro j;exact (input5_join R tag index pre j).symm
  · intro j;fin_cases j <;>rfl
  · intro j;exact (bank5_slot R tag index pre j).symm
  · intro i hi
    refine ⟨?_,(bank5_other R tag index pre i hi).symm⟩
    have hn : i≠2 := by intro h;subst i;exact hi 35 rfl
    simp [heads,hn]
def joined5 := Composition.machine joined4 phase5
def budget5 (R tag index : Nat) := budget4 R tag index+1+cost5 R tag index
theorem run5 (R tag index : Nat) (pre : List Bool) : Step joined5 (budget5 R tag index)
    (heads pre) (input R tag index pre) (heads (next tag index pre)) (bank5 R tag index pre) :=
  (run4 R tag index pre).seq (step5 R tag index pre)

abbrev machine := joined5
abbrev budget := budget5
abbrev output := bank5
abbrev run := run5

theorem tag_out (R tag index : Nat) (pre : List Bool) : output R tag index pre 0=UWalkUnary.source R tag := by
  change bank5 R tag index pre 0=_
  rw [bank5_other R tag index pre 0 (by decide)]
  rw [bank4_other R tag index pre 0 (by decide)]
  rw [bank3_other R tag index pre 0 (by decide)]
  rw [bank2_other R tag index pre 0 (by decide)]
  change bank1 R tag index pre (slots1 0)=_
  rw [bank1_slot]
  rfl

theorem index_out (R tag index : Nat) (pre : List Bool) : output R tag index pre 1=UWalkUnary.source R index := by
  change bank5 R tag index pre 1=_
  rw [bank5_other R tag index pre 1 (by decide)]
  rw [bank4_other R tag index pre 1 (by decide)]
  change bank3 R tag index pre (slots3 0)=_
  rw [bank3_slot]
  rfl

theorem record_out (R tag index : Nat) (pre : List Bool) : output R tag index pre 2=next tag index pre := by
  change bank5 R tag index pre 2=_
  change bank5 R tag index pre (slots5 35)=_
  rw [bank5_slot]
  exact value5 R tag index pre

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairUnary
