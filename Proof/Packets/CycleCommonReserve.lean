import Proof.Packets.UnaryAffine
import Proof.Packets.CycleLiveSuccessor
import Proof.CaseAnalysis.CapacityPower

/-! A fixed 48-tape program physically generates the shared reset reserve
65536*(B+1)^4*2^(8*w) from the measured pool and chosen width templates.
The constant 65536 is generated as 2^16 by paid arithmetic. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleCommonReserve
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairSource
open NearCubicWires.RepairSource.VerifierDecoding
open Completion
noncomputable section

def reserve (B w : Nat) := 65536*(B+1)^4*2^(8*w)
def exponent (w : Nat) := 8*w+16

theorem value_eq (B w : Nat) : (B+1)^4*2^exponent w=reserve B w := by
  unfold exponent reserve
  rw [pow_add]
  norm_num
  ring

theorem of_clock {t st n : Nat} {p : Machine t st} {A B : Fin t→List Bool}
    (h : ClockJoin.ReadyRun p n A B) : Step p n (fun _=>0) A (fun _=>0) B := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,funext hh,ht,hs⟩

def input1 (B _w : Nat) := UWalkUnary.input (B+2) B
def output1 (B _w : Nat) := UWalkUnary.result false true (B+2) B
def worker1 := UWalkUnary.machine false true
def cost1 (B _w : Nat) := 2*B+6
theorem local1 (B w : Nat) : Step worker1 (cost1 B w)
    (fun _=>0) (input1 B w) (fun _=>0) (output1 B w) :=
  of_clock (UWalkUnary.ready false true (B+2) B)

def input2 (B _w : Nat) := DimensionTemplate.input (B+1)
def output2 (B _w : Nat) := DimensionTemplate.output false (B+1)
def worker2 := DimensionTemplate.machine false
def cost2 (B _w : Nat) := 2*(B+1)+8
theorem local2 (B w : Nat) : Step worker2 (cost2 B w)
    (fun _=>0) (input2 B w) (fun _=>0) (output2 B w) :=
  of_clock (DimensionTemplate.ready false (B+1))

def input3 (B _w : Nat) : Fin 11→List Bool := DimensionPower.input 4 (B+1)
def output3 (B _w : Nat) : Fin 11→List Bool := Classical.choose (DimensionPower.power_run 4 1 (B+1))
def worker3 := DimensionPower.machine 4 1
def cost3 (B _w : Nat) := DimensionPower.cost 1 (B+1) 4
theorem local3 (B w : Nat) : Step worker3 (cost3 B w)
    (fun _=>0) (input3 B w) (fun _=>0) (output3 B w) :=
  of_clock (Classical.choose_spec (DimensionPower.power_run 4 1 (B+1))).1
theorem output3_value (B w : Nat) : output3 B w 9=List.replicate ((B+1)^4) true := by
  have hi : DimensionPower.valueSlot 4 4 (by omega)=(9 : Fin 11) := by decide
  have h := (Classical.choose_spec (DimensionPower.power_run 4 1 (B+1))).2.2
  exact (congrArg (output3 B w) hi.symm).trans
    (h.trans (congrArg (fun n=>List.replicate n true) (Nat.one_mul _)))

def input4 (_B w : Nat) := UWalkUnary.input (w+2) w
def output4 (_B w : Nat) := UWalkUnary.result false false (w+2) w
def worker4 := UWalkUnary.machine false false
def cost4 (_B w : Nat) := 2*w+6
theorem local4 (B w : Nat) : Step worker4 (cost4 B w)
    (fun _=>0) (input4 B w) (fun _=>0) (output4 B w) :=
  of_clock (UWalkUnary.ready false false (w+2) w)

def input5 (_B w : Nat) := UnaryAffine.input w
def output5 (_B w : Nat) := Classical.choose (UnaryAffine.run w 8 16)
def worker5 := UnaryAffine.machine 8 16
def cost5 (_B w : Nat) := UnaryAffine.budget w 8 16
theorem local5 (B w : Nat) : Step worker5 (cost5 B w)
    (fun _=>0) (input5 B w) (fun _=>0) (output5 B w) :=
  (Classical.choose_spec (UnaryAffine.run w 8 16)).1
theorem output5_value (B w : Nat) : output5 B w 9=List.replicate (exponent w) true :=
  (Classical.choose_spec (UnaryAffine.run w 8 16)).2.2

def input6 (_B w : Nat) := CloseoutCapacity.Power.input (exponent w)
def output6 (_B w : Nat) := Classical.choose (CloseoutCapacity.Power.power_run (exponent w))
def worker6 := CloseoutCapacity.Power.machine
def cost6 (_B w : Nat) := CloseoutCapacity.Power.budget (exponent w)
theorem local6 (B w : Nat) : Step worker6 (cost6 B w)
    (fun _=>0) (input6 B w) (fun _=>0) (output6 B w) :=
  of_clock (Classical.choose_spec (CloseoutCapacity.Power.power_run (exponent w))).1
theorem output6_template (B w : Nat) : output6 B w 13=UnaryTemplate.tape (2^exponent w) :=
  (Classical.choose_spec (CloseoutCapacity.Power.power_run (exponent w))).2.2

def input7 (B w : Nat) := WilliamsUnaryProduct.input ((B+1)^4) (2^exponent w)
def output7 (B w : Nat) := WilliamsUnaryProduct.output ((B+1)^4) (2^exponent w)
def worker7 := ClockUnaryProduct.machine
def cost7 (B w : Nat) := WilliamsUnaryProduct.budget ((B+1)^4) (2^exponent w)
theorem local7 (B w : Nat) : Step worker7 (cost7 B w)
    (fun _=>0) (input7 B w) (fun _=>0) (output7 B w) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=WilliamsUnaryProduct.product_ready ((B+1)^4) (2^exponent w)
  exact ⟨r,hr,funext hh,ht,hs.le⟩

def input8 (B w : Nat) := DimensionTemplate.input (reserve B w)
def output8 (B w : Nat) := DimensionTemplate.output false (reserve B w)
def worker8 := DimensionTemplate.machine false
def cost8 (B w : Nat) := 2*reserve B w+8
theorem local8 (B w : Nat) : Step worker8 (cost8 B w)
    (fun _=>0) (input8 B w) (fun _=>0) (output8 B w) :=
  of_clock (DimensionTemplate.ready false (reserve B w))

def input (B w : Nat) (i : Fin 48) : List Bool :=
  if i=0 then UnaryTemplate.tape B else if i=1 then UnaryTemplate.tape w else []
-- BEGIN GENERATED WIRING

def slots1 : Fin 3→Fin 48 := ![0,2,3]
theorem injective1 : Function.Injective slots1 := by decide
def phase1 := RecoveryFocus.machine slots1 worker1
def bank1 (B w : Nat) := install slots1 (input B w) (output1 B w)
theorem bank1_slot (B w : Nat) (j : Fin 3) : bank1 B w (slots1 j)=output1 B w j :=
  install_slot slots1 injective1 _ _ j
theorem bank1_other (B w : Nat) (i : Fin 48) (hi : ∀ j,slots1 j≠i) : bank1 B w i=input B w i :=
  install_other slots1 _ _ _ hi

theorem input1_join (B w : Nat) : ∀ j,input B w (slots1 j)=input1 B w j := by
  intro j
  fin_cases j
  · change input B w 0=input1 B w 0
    exact (CycleLiveSuccessor.source_eq B).symm
  · change input B w 2=input1 B w 1
    rfl
  · change input B w 3=input1 B w 2
    rfl
theorem step1 (B w : Nat) : Step phase1 (cost1 B w) (fun _=>0) (input B w)
    (fun _=>0) (bank1 B w) := by
  have h:=(local1 B w).focus slots1 injective1 (fun _=>0) (input B w)
  have hz : dockH slots1 (fun _ : Fin 48=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots1 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input1_join B w))).congr hz rfl
def joined1 := phase1
def budget1 (B w : Nat) := cost1 B w
theorem run1 (B w : Nat) : Step joined1 (budget1 B w) (fun _=>0) (input B w) (fun _=>0) (bank1 B w) := step1 B w

def slots2 : Fin 3→Fin 48 := ![2,4,5]
theorem injective2 : Function.Injective slots2 := by decide
def phase2 := RecoveryFocus.machine slots2 worker2
def bank2 (B w : Nat) := install slots2 (bank1 B w) (output2 B w)
theorem bank2_slot (B w : Nat) (j : Fin 3) : bank2 B w (slots2 j)=output2 B w j :=
  install_slot slots2 injective2 _ _ j
theorem bank2_other (B w : Nat) (i : Fin 48) (hi : ∀ j,slots2 j≠i) : bank2 B w i=bank1 B w i :=
  install_other slots2 _ _ _ hi

theorem input2_join (B w : Nat) : ∀ j,bank1 B w (slots2 j)=input2 B w j := by
  intro j
  fin_cases j
  · change bank1 B w 2=input2 B w 0
    change bank1 B w (slots1 1)=_
    rw [bank1_slot]
    simp [output1,input2,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,DimensionTemplate.input]
  · change bank1 B w 4=input2 B w 1
    rw [bank1_other B w 4 (by decide)]
    rfl
  · change bank1 B w 5=input2 B w 2
    rw [bank1_other B w 5 (by decide)]
    rfl
theorem step2 (B w : Nat) : Step phase2 (cost2 B w) (fun _=>0) (bank1 B w)
    (fun _=>0) (bank2 B w) := by
  have h:=(local2 B w).focus slots2 injective2 (fun _=>0) (bank1 B w)
  have hz : dockH slots2 (fun _ : Fin 48=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots2 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input2_join B w))).congr hz rfl
def joined2 := Composition.machine joined1 phase2
def budget2 (B w : Nat) := budget1 B w+1+cost2 B w
theorem run2 (B w : Nat) : Step joined2 (budget2 B w) (fun _=>0) (input B w) (fun _=>0) (bank2 B w) :=
  (run1 B w).seq (step2 B w)

def slots3 : Fin 11→Fin 48 := ![4,6,7,8,9,10,11,12,13,14,15]
theorem injective3 : Function.Injective slots3 := by decide
def phase3 := RecoveryFocus.machine slots3 worker3
def bank3 (B w : Nat) := install slots3 (bank2 B w) (output3 B w)
theorem bank3_slot (B w : Nat) (j : Fin 11) : bank3 B w (slots3 j)=output3 B w j :=
  install_slot slots3 injective3 _ _ j
theorem bank3_other (B w : Nat) (i : Fin 48) (hi : ∀ j,slots3 j≠i) : bank3 B w i=bank2 B w i :=
  install_other slots3 _ _ _ hi

theorem input3_join (B w : Nat) : ∀ j,bank2 B w (slots3 j)=input3 B w j := by
  intro j
  fin_cases j
  · change bank2 B w 4=input3 B w 0
    change bank2 B w (slots2 1)=_
    rw [bank2_slot]
    rfl
  · change bank2 B w 6=input3 B w 1
    rw [bank2_other B w 6 (by decide)]
    rw [bank1_other B w 6 (by decide)]
    rfl
  · change bank2 B w 7=input3 B w 2
    rw [bank2_other B w 7 (by decide)]
    rw [bank1_other B w 7 (by decide)]
    rfl
  · change bank2 B w 8=input3 B w 3
    rw [bank2_other B w 8 (by decide)]
    rw [bank1_other B w 8 (by decide)]
    rfl
  · change bank2 B w 9=input3 B w 4
    rw [bank2_other B w 9 (by decide)]
    rw [bank1_other B w 9 (by decide)]
    rfl
  · change bank2 B w 10=input3 B w 5
    rw [bank2_other B w 10 (by decide)]
    rw [bank1_other B w 10 (by decide)]
    rfl
  · change bank2 B w 11=input3 B w 6
    rw [bank2_other B w 11 (by decide)]
    rw [bank1_other B w 11 (by decide)]
    rfl
  · change bank2 B w 12=input3 B w 7
    rw [bank2_other B w 12 (by decide)]
    rw [bank1_other B w 12 (by decide)]
    rfl
  · change bank2 B w 13=input3 B w 8
    rw [bank2_other B w 13 (by decide)]
    rw [bank1_other B w 13 (by decide)]
    rfl
  · change bank2 B w 14=input3 B w 9
    rw [bank2_other B w 14 (by decide)]
    rw [bank1_other B w 14 (by decide)]
    rfl
  · change bank2 B w 15=input3 B w 10
    rw [bank2_other B w 15 (by decide)]
    rw [bank1_other B w 15 (by decide)]
    rfl
theorem step3 (B w : Nat) : Step phase3 (cost3 B w) (fun _=>0) (bank2 B w)
    (fun _=>0) (bank3 B w) := by
  have h:=(local3 B w).focus slots3 injective3 (fun _=>0) (bank2 B w)
  have hz : dockH slots3 (fun _ : Fin 48=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots3 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input3_join B w))).congr hz rfl
def joined3 := Composition.machine joined2 phase3
def budget3 (B w : Nat) := budget2 B w+1+cost3 B w
theorem run3 (B w : Nat) : Step joined3 (budget3 B w) (fun _=>0) (input B w) (fun _=>0) (bank3 B w) :=
  (run2 B w).seq (step3 B w)

def slots4 : Fin 3→Fin 48 := ![1,16,17]
theorem injective4 : Function.Injective slots4 := by decide
def phase4 := RecoveryFocus.machine slots4 worker4
def bank4 (B w : Nat) := install slots4 (bank3 B w) (output4 B w)
theorem bank4_slot (B w : Nat) (j : Fin 3) : bank4 B w (slots4 j)=output4 B w j :=
  install_slot slots4 injective4 _ _ j
theorem bank4_other (B w : Nat) (i : Fin 48) (hi : ∀ j,slots4 j≠i) : bank4 B w i=bank3 B w i :=
  install_other slots4 _ _ _ hi

theorem input4_join (B w : Nat) : ∀ j,bank3 B w (slots4 j)=input4 B w j := by
  intro j
  fin_cases j
  · change bank3 B w 1=input4 B w 0
    rw [bank3_other B w 1 (by decide)]
    rw [bank2_other B w 1 (by decide)]
    rw [bank1_other B w 1 (by decide)]
    exact (CycleLiveSuccessor.source_eq w).symm
  · change bank3 B w 16=input4 B w 1
    rw [bank3_other B w 16 (by decide)]
    rw [bank2_other B w 16 (by decide)]
    rw [bank1_other B w 16 (by decide)]
    rfl
  · change bank3 B w 17=input4 B w 2
    rw [bank3_other B w 17 (by decide)]
    rw [bank2_other B w 17 (by decide)]
    rw [bank1_other B w 17 (by decide)]
    rfl
theorem step4 (B w : Nat) : Step phase4 (cost4 B w) (fun _=>0) (bank3 B w)
    (fun _=>0) (bank4 B w) := by
  have h:=(local4 B w).focus slots4 injective4 (fun _=>0) (bank3 B w)
  have hz : dockH slots4 (fun _ : Fin 48=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots4 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input4_join B w))).congr hz rfl
def joined4 := Composition.machine joined3 phase4
def budget4 (B w : Nat) := budget3 B w+1+cost4 B w
theorem run4 (B w : Nat) : Step joined4 (budget4 B w) (fun _=>0) (input B w) (fun _=>0) (bank4 B w) :=
  (run3 B w).seq (step4 B w)

def slots5 : Fin 11→Fin 48 := ![16,18,19,20,21,22,23,24,25,26,27]
theorem injective5 : Function.Injective slots5 := by decide
def phase5 := RecoveryFocus.machine slots5 worker5
def bank5 (B w : Nat) := install slots5 (bank4 B w) (output5 B w)
theorem bank5_slot (B w : Nat) (j : Fin 11) : bank5 B w (slots5 j)=output5 B w j :=
  install_slot slots5 injective5 _ _ j
theorem bank5_other (B w : Nat) (i : Fin 48) (hi : ∀ j,slots5 j≠i) : bank5 B w i=bank4 B w i :=
  install_other slots5 _ _ _ hi

theorem input5_join (B w : Nat) : ∀ j,bank4 B w (slots5 j)=input5 B w j := by
  intro j
  fin_cases j
  · change bank4 B w 16=input5 B w 0
    change bank4 B w (slots4 1)=_
    rw [bank4_slot]
    simp [output4,input5,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,UnaryAffine.input]
  · change bank4 B w 18=input5 B w 1
    rw [bank4_other B w 18 (by decide)]
    rw [bank3_other B w 18 (by decide)]
    rw [bank2_other B w 18 (by decide)]
    rw [bank1_other B w 18 (by decide)]
    rfl
  · change bank4 B w 19=input5 B w 2
    rw [bank4_other B w 19 (by decide)]
    rw [bank3_other B w 19 (by decide)]
    rw [bank2_other B w 19 (by decide)]
    rw [bank1_other B w 19 (by decide)]
    rfl
  · change bank4 B w 20=input5 B w 3
    rw [bank4_other B w 20 (by decide)]
    rw [bank3_other B w 20 (by decide)]
    rw [bank2_other B w 20 (by decide)]
    rw [bank1_other B w 20 (by decide)]
    rfl
  · change bank4 B w 21=input5 B w 4
    rw [bank4_other B w 21 (by decide)]
    rw [bank3_other B w 21 (by decide)]
    rw [bank2_other B w 21 (by decide)]
    rw [bank1_other B w 21 (by decide)]
    rfl
  · change bank4 B w 22=input5 B w 5
    rw [bank4_other B w 22 (by decide)]
    rw [bank3_other B w 22 (by decide)]
    rw [bank2_other B w 22 (by decide)]
    rw [bank1_other B w 22 (by decide)]
    rfl
  · change bank4 B w 23=input5 B w 6
    rw [bank4_other B w 23 (by decide)]
    rw [bank3_other B w 23 (by decide)]
    rw [bank2_other B w 23 (by decide)]
    rw [bank1_other B w 23 (by decide)]
    rfl
  · change bank4 B w 24=input5 B w 7
    rw [bank4_other B w 24 (by decide)]
    rw [bank3_other B w 24 (by decide)]
    rw [bank2_other B w 24 (by decide)]
    rw [bank1_other B w 24 (by decide)]
    rfl
  · change bank4 B w 25=input5 B w 8
    rw [bank4_other B w 25 (by decide)]
    rw [bank3_other B w 25 (by decide)]
    rw [bank2_other B w 25 (by decide)]
    rw [bank1_other B w 25 (by decide)]
    rfl
  · change bank4 B w 26=input5 B w 9
    rw [bank4_other B w 26 (by decide)]
    rw [bank3_other B w 26 (by decide)]
    rw [bank2_other B w 26 (by decide)]
    rw [bank1_other B w 26 (by decide)]
    rfl
  · change bank4 B w 27=input5 B w 10
    rw [bank4_other B w 27 (by decide)]
    rw [bank3_other B w 27 (by decide)]
    rw [bank2_other B w 27 (by decide)]
    rw [bank1_other B w 27 (by decide)]
    rfl
theorem step5 (B w : Nat) : Step phase5 (cost5 B w) (fun _=>0) (bank4 B w)
    (fun _=>0) (bank5 B w) := by
  have h:=(local5 B w).focus slots5 injective5 (fun _=>0) (bank4 B w)
  have hz : dockH slots5 (fun _ : Fin 48=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots5 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input5_join B w))).congr hz rfl
def joined5 := Composition.machine joined4 phase5
def budget5 (B w : Nat) := budget4 B w+1+cost5 B w
theorem run5 (B w : Nat) : Step joined5 (budget5 B w) (fun _=>0) (input B w) (fun _=>0) (bank5 B w) :=
  (run4 B w).seq (step5 B w)

def slots6 : Fin 17→Fin 48 := ![26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43]
theorem injective6 : Function.Injective slots6 := by decide
def phase6 := RecoveryFocus.machine slots6 worker6
def bank6 (B w : Nat) := install slots6 (bank5 B w) (output6 B w)
theorem bank6_slot (B w : Nat) (j : Fin 17) : bank6 B w (slots6 j)=output6 B w j :=
  install_slot slots6 injective6 _ _ j
theorem bank6_other (B w : Nat) (i : Fin 48) (hi : ∀ j,slots6 j≠i) : bank6 B w i=bank5 B w i :=
  install_other slots6 _ _ _ hi

theorem input6_join (B w : Nat) : ∀ j,bank5 B w (slots6 j)=input6 B w j := by
  intro j
  fin_cases j
  · change bank5 B w 26=input6 B w 0
    change bank5 B w (slots5 9)=_
    rw [bank5_slot]
    exact output5_value B w
  · change bank5 B w 28=input6 B w 1
    rw [bank5_other B w 28 (by decide)]
    rw [bank4_other B w 28 (by decide)]
    rw [bank3_other B w 28 (by decide)]
    rw [bank2_other B w 28 (by decide)]
    rw [bank1_other B w 28 (by decide)]
    rfl
  · change bank5 B w 29=input6 B w 2
    rw [bank5_other B w 29 (by decide)]
    rw [bank4_other B w 29 (by decide)]
    rw [bank3_other B w 29 (by decide)]
    rw [bank2_other B w 29 (by decide)]
    rw [bank1_other B w 29 (by decide)]
    rfl
  · change bank5 B w 30=input6 B w 3
    rw [bank5_other B w 30 (by decide)]
    rw [bank4_other B w 30 (by decide)]
    rw [bank3_other B w 30 (by decide)]
    rw [bank2_other B w 30 (by decide)]
    rw [bank1_other B w 30 (by decide)]
    rfl
  · change bank5 B w 31=input6 B w 4
    rw [bank5_other B w 31 (by decide)]
    rw [bank4_other B w 31 (by decide)]
    rw [bank3_other B w 31 (by decide)]
    rw [bank2_other B w 31 (by decide)]
    rw [bank1_other B w 31 (by decide)]
    rfl
  · change bank5 B w 32=input6 B w 5
    rw [bank5_other B w 32 (by decide)]
    rw [bank4_other B w 32 (by decide)]
    rw [bank3_other B w 32 (by decide)]
    rw [bank2_other B w 32 (by decide)]
    rw [bank1_other B w 32 (by decide)]
    rfl
  · change bank5 B w 33=input6 B w 6
    rw [bank5_other B w 33 (by decide)]
    rw [bank4_other B w 33 (by decide)]
    rw [bank3_other B w 33 (by decide)]
    rw [bank2_other B w 33 (by decide)]
    rw [bank1_other B w 33 (by decide)]
    rfl
  · change bank5 B w 34=input6 B w 7
    rw [bank5_other B w 34 (by decide)]
    rw [bank4_other B w 34 (by decide)]
    rw [bank3_other B w 34 (by decide)]
    rw [bank2_other B w 34 (by decide)]
    rw [bank1_other B w 34 (by decide)]
    rfl
  · change bank5 B w 35=input6 B w 8
    rw [bank5_other B w 35 (by decide)]
    rw [bank4_other B w 35 (by decide)]
    rw [bank3_other B w 35 (by decide)]
    rw [bank2_other B w 35 (by decide)]
    rw [bank1_other B w 35 (by decide)]
    rfl
  · change bank5 B w 36=input6 B w 9
    rw [bank5_other B w 36 (by decide)]
    rw [bank4_other B w 36 (by decide)]
    rw [bank3_other B w 36 (by decide)]
    rw [bank2_other B w 36 (by decide)]
    rw [bank1_other B w 36 (by decide)]
    rfl
  · change bank5 B w 37=input6 B w 10
    rw [bank5_other B w 37 (by decide)]
    rw [bank4_other B w 37 (by decide)]
    rw [bank3_other B w 37 (by decide)]
    rw [bank2_other B w 37 (by decide)]
    rw [bank1_other B w 37 (by decide)]
    rfl
  · change bank5 B w 38=input6 B w 11
    rw [bank5_other B w 38 (by decide)]
    rw [bank4_other B w 38 (by decide)]
    rw [bank3_other B w 38 (by decide)]
    rw [bank2_other B w 38 (by decide)]
    rw [bank1_other B w 38 (by decide)]
    rfl
  · change bank5 B w 39=input6 B w 12
    rw [bank5_other B w 39 (by decide)]
    rw [bank4_other B w 39 (by decide)]
    rw [bank3_other B w 39 (by decide)]
    rw [bank2_other B w 39 (by decide)]
    rw [bank1_other B w 39 (by decide)]
    rfl
  · change bank5 B w 40=input6 B w 13
    rw [bank5_other B w 40 (by decide)]
    rw [bank4_other B w 40 (by decide)]
    rw [bank3_other B w 40 (by decide)]
    rw [bank2_other B w 40 (by decide)]
    rw [bank1_other B w 40 (by decide)]
    rfl
  · change bank5 B w 41=input6 B w 14
    rw [bank5_other B w 41 (by decide)]
    rw [bank4_other B w 41 (by decide)]
    rw [bank3_other B w 41 (by decide)]
    rw [bank2_other B w 41 (by decide)]
    rw [bank1_other B w 41 (by decide)]
    rfl
  · change bank5 B w 42=input6 B w 15
    rw [bank5_other B w 42 (by decide)]
    rw [bank4_other B w 42 (by decide)]
    rw [bank3_other B w 42 (by decide)]
    rw [bank2_other B w 42 (by decide)]
    rw [bank1_other B w 42 (by decide)]
    rfl
  · change bank5 B w 43=input6 B w 16
    rw [bank5_other B w 43 (by decide)]
    rw [bank4_other B w 43 (by decide)]
    rw [bank3_other B w 43 (by decide)]
    rw [bank2_other B w 43 (by decide)]
    rw [bank1_other B w 43 (by decide)]
    rfl
theorem step6 (B w : Nat) : Step phase6 (cost6 B w) (fun _=>0) (bank5 B w)
    (fun _=>0) (bank6 B w) := by
  have h:=(local6 B w).focus slots6 injective6 (fun _=>0) (bank5 B w)
  have hz : dockH slots6 (fun _ : Fin 48=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots6 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input6_join B w))).congr hz rfl
def joined6 := Composition.machine joined5 phase6
def budget6 (B w : Nat) := budget5 B w+1+cost6 B w
theorem run6 (B w : Nat) : Step joined6 (budget6 B w) (fun _=>0) (input B w) (fun _=>0) (bank6 B w) :=
  (run5 B w).seq (step6 B w)

def slots7 : Fin 4→Fin 48 := ![14,40,44,45]
theorem injective7 : Function.Injective slots7 := by decide
def phase7 := RecoveryFocus.machine slots7 worker7
def bank7 (B w : Nat) := install slots7 (bank6 B w) (output7 B w)
theorem bank7_slot (B w : Nat) (j : Fin 4) : bank7 B w (slots7 j)=output7 B w j :=
  install_slot slots7 injective7 _ _ j
theorem bank7_other (B w : Nat) (i : Fin 48) (hi : ∀ j,slots7 j≠i) : bank7 B w i=bank6 B w i :=
  install_other slots7 _ _ _ hi

theorem input7_join (B w : Nat) : ∀ j,bank6 B w (slots7 j)=input7 B w j := by
  intro j
  fin_cases j
  · change bank6 B w 14=input7 B w 0
    rw [bank6_other B w 14 (by decide)]
    rw [bank5_other B w 14 (by decide)]
    rw [bank4_other B w 14 (by decide)]
    change bank3 B w (slots3 9)=_
    rw [bank3_slot]
    exact output3_value B w
  · change bank6 B w 40=input7 B w 1
    change bank6 B w (slots6 13)=_
    rw [bank6_slot]
    exact output6_template B w
  · change bank6 B w 44=input7 B w 2
    rw [bank6_other B w 44 (by decide)]
    rw [bank5_other B w 44 (by decide)]
    rw [bank4_other B w 44 (by decide)]
    rw [bank3_other B w 44 (by decide)]
    rw [bank2_other B w 44 (by decide)]
    rw [bank1_other B w 44 (by decide)]
    rfl
  · change bank6 B w 45=input7 B w 3
    rw [bank6_other B w 45 (by decide)]
    rw [bank5_other B w 45 (by decide)]
    rw [bank4_other B w 45 (by decide)]
    rw [bank3_other B w 45 (by decide)]
    rw [bank2_other B w 45 (by decide)]
    rw [bank1_other B w 45 (by decide)]
    rfl
theorem step7 (B w : Nat) : Step phase7 (cost7 B w) (fun _=>0) (bank6 B w)
    (fun _=>0) (bank7 B w) := by
  have h:=(local7 B w).focus slots7 injective7 (fun _=>0) (bank6 B w)
  have hz : dockH slots7 (fun _ : Fin 48=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots7 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input7_join B w))).congr hz rfl
def joined7 := Composition.machine joined6 phase7
def budget7 (B w : Nat) := budget6 B w+1+cost7 B w
theorem run7 (B w : Nat) : Step joined7 (budget7 B w) (fun _=>0) (input B w) (fun _=>0) (bank7 B w) :=
  (run6 B w).seq (step7 B w)

def slots8 : Fin 3→Fin 48 := ![44,46,47]
theorem injective8 : Function.Injective slots8 := by decide
def phase8 := RecoveryFocus.machine slots8 worker8
def bank8 (B w : Nat) := install slots8 (bank7 B w) (output8 B w)
theorem bank8_slot (B w : Nat) (j : Fin 3) : bank8 B w (slots8 j)=output8 B w j :=
  install_slot slots8 injective8 _ _ j
theorem bank8_other (B w : Nat) (i : Fin 48) (hi : ∀ j,slots8 j≠i) : bank8 B w i=bank7 B w i :=
  install_other slots8 _ _ _ hi

theorem input8_join (B w : Nat) : ∀ j,bank7 B w (slots8 j)=input8 B w j := by
  intro j
  fin_cases j
  · change bank7 B w 44=input8 B w 0
    change bank7 B w (slots7 2)=_
    rw [bank7_slot]
    change List.replicate ((B+1)^4*2^exponent w) true=List.replicate (reserve B w) true
    rw [value_eq]
  · change bank7 B w 46=input8 B w 1
    rw [bank7_other B w 46 (by decide)]
    rw [bank6_other B w 46 (by decide)]
    rw [bank5_other B w 46 (by decide)]
    rw [bank4_other B w 46 (by decide)]
    rw [bank3_other B w 46 (by decide)]
    rw [bank2_other B w 46 (by decide)]
    rw [bank1_other B w 46 (by decide)]
    rfl
  · change bank7 B w 47=input8 B w 2
    rw [bank7_other B w 47 (by decide)]
    rw [bank6_other B w 47 (by decide)]
    rw [bank5_other B w 47 (by decide)]
    rw [bank4_other B w 47 (by decide)]
    rw [bank3_other B w 47 (by decide)]
    rw [bank2_other B w 47 (by decide)]
    rw [bank1_other B w 47 (by decide)]
    rfl
theorem step8 (B w : Nat) : Step phase8 (cost8 B w) (fun _=>0) (bank7 B w)
    (fun _=>0) (bank8 B w) := by
  have h:=(local8 B w).focus slots8 injective8 (fun _=>0) (bank7 B w)
  have hz : dockH slots8 (fun _ : Fin 48=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots8 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input8_join B w))).congr hz rfl
def joined8 := Composition.machine joined7 phase8
def budget8 (B w : Nat) := budget7 B w+1+cost8 B w
theorem run8 (B w : Nat) : Step joined8 (budget8 B w) (fun _=>0) (input B w) (fun _=>0) (bank8 B w) :=
  (run7 B w).seq (step8 B w)

abbrev machine := joined8
abbrev budget := budget8
abbrev output := bank8

theorem run (B w : Nat) : Step machine (budget B w)
    (fun _=>0) (input B w) (fun _=>0) (output B w) := run8 B w

theorem raw_reserve (B w : Nat) : output B w 44=List.replicate (reserve B w) true :=
  bank8_slot B w 0

end
end Theorem25Completion.CycleCommonReserve
