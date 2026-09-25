import Proof.PCP.ProjectionDimensionTemplate
import Proof.Packets.CycleLiveSuccessor

/-! Produce the framed support-record width W=2B+3 from the actual measured
pool-count template. The fixed worker emits every scalar and returns with W's
cursor at its first unary mark, as required by the physical normalizer. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleMaskWidth
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairSource.ProjectionNormalization
noncomputable section

theorem of_clock {t st n : Nat} {p : Machine t st} {A B : Fin t→List Bool}
    (h : ClockJoin.ReadyRun p n A B) : Step p n (fun _=>0) A (fun _=>0) B := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,funext hh,ht,hs⟩

def input1 (B : Nat) : Fin 3→List Bool := ![UnaryTemplate.tape B,[],[]]
def output1 (B : Nat) : Fin 3→List Bool :=
  ![UnaryTemplate.tape B,List.replicate B true,List.replicate (B+2) false]
def worker1 := UWalkUnary.machine false false
def cost1 (B : Nat) := 2*B+6
theorem local1 (B : Nat) : Step worker1 (cost1 B) (fun _=>0) (input1 B) (fun _=>0) (output1 B) := by
  have h:=of_clock (UWalkUnary.ready false false (B+2) B)
  apply (h.congr_in rfl ?_).congr rfl ?_
  all_goals funext i;fin_cases i <;>simp [UWalkUnary.input,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,
    input1,output1,CycleLiveSuccessor.source_eq]

def input2 (B : Nat) := DimensionTemplate.input B
def output2 (B : Nat) := DimensionTemplate.output true B
def worker2 := DimensionTemplate.machine true
def cost2 (B : Nat) := 2*B+8
theorem local2 (B : Nat) : Step worker2 (cost2 B) (fun _=>0) (input2 B) (fun _=>0) (output2 B) :=
  of_clock (DimensionTemplate.ready true B)

def input3 (B : Nat) : Fin 5→List Bool := DimensionPower.input 1 (B+1)
def output3 (B : Nat) : Fin 5→List Bool := Classical.choose (DimensionPower.power_run 1 2 (B+1))
def worker3 := DimensionPower.machine 1 2
def cost3 (B : Nat) := DimensionPower.cost 2 (B+1) 1
theorem local3 (B : Nat) : Step worker3 (cost3 B) (fun _=>0) (input3 B) (fun _=>0) (output3 B) :=
  of_clock (Classical.choose_spec (DimensionPower.power_run 1 2 (B+1))).1
theorem output3_value (B : Nat) : output3 B 3=List.replicate (2*(B+1)) true := by
  have h := (Classical.choose_spec (DimensionPower.power_run 1 2 (B+1))).2.2
  change output3 B (DimensionPower.valueSlot 1 1 le_rfl)=List.replicate (2*(B+1)^1) true at h
  have hi : DimensionPower.valueSlot 1 1 le_rfl=(3 : Fin 5) := by decide
  rw [hi,pow_one] at h
  exact h

def input4 (B : Nat) := DimensionTemplate.input (2*(B+1))
def output4 (B : Nat) := DimensionTemplate.output true (2*(B+1))
def worker4 := DimensionTemplate.machine true
def cost4 (B : Nat) := 2*(2*(B+1))+8
theorem local4 (B : Nat) : Step worker4 (cost4 B) (fun _=>0) (input4 B) (fun _=>0) (output4 B) :=
  of_clock (DimensionTemplate.ready true (2*(B+1)))

def input (B : Nat) (i : Fin 11) : List Bool := if i=0 then UnaryTemplate.tape B else []
-- BEGIN GENERATED

def slots1 : Fin 3→Fin 11 := ![0,1,2]
theorem injective1 : Function.Injective slots1 := by decide
def phase1 := RecoveryFocus.machine slots1 worker1
def bank1 (B : Nat) := install slots1 (input B) (output1 B)
theorem bank1_slot (B : Nat) (j : Fin 3) : bank1 B (slots1 j)=output1 B j :=
  install_slot slots1 injective1 _ _ j
theorem bank1_other (B : Nat) (i : Fin 11) (hi : ∀ j,slots1 j≠i) : bank1 B i=input B i :=
  install_other slots1 _ _ _ hi

theorem input1_join (B : Nat) : ∀ j,input B (slots1 j)=input1 B j := by
  intro j
  fin_cases j
  · change input B 0=input1 B 0
    rfl
  · change input B 1=input1 B 1
    rfl
  · change input B 2=input1 B 2
    rfl
theorem step1 (B : Nat) : Step phase1 (cost1 B) (fun _=>0) (input B)
    (fun _=>0) (bank1 B) := by
  have h:=(local1 B).focus slots1 injective1 (fun _=>0) (input B)
  have hz : dockH slots1 (fun _ : Fin 11=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots1 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input1_join B))).congr hz rfl
def joined1 := phase1
def budget1 (B : Nat) := cost1 B
theorem run1 (B : Nat) : Step joined1 (budget1 B) (fun _=>0) (input B) (fun _=>0) (bank1 B) := step1 B

def slots2 : Fin 3→Fin 11 := ![1,3,4]
theorem injective2 : Function.Injective slots2 := by decide
def phase2 := RecoveryFocus.machine slots2 worker2
def bank2 (B : Nat) := install slots2 (bank1 B) (output2 B)
theorem bank2_slot (B : Nat) (j : Fin 3) : bank2 B (slots2 j)=output2 B j :=
  install_slot slots2 injective2 _ _ j
theorem bank2_other (B : Nat) (i : Fin 11) (hi : ∀ j,slots2 j≠i) : bank2 B i=bank1 B i :=
  install_other slots2 _ _ _ hi

theorem input2_join (B : Nat) : ∀ j,bank1 B (slots2 j)=input2 B j := by
  intro j
  fin_cases j
  · change bank1 B 1=input2 B 0
    change bank1 B (slots1 1)=_
    rw [bank1_slot]
    rfl
  · change bank1 B 3=input2 B 1
    rw [bank1_other B 3 (by decide)]
    rfl
  · change bank1 B 4=input2 B 2
    rw [bank1_other B 4 (by decide)]
    rfl
theorem step2 (B : Nat) : Step phase2 (cost2 B) (fun _=>0) (bank1 B)
    (fun _=>0) (bank2 B) := by
  have h:=(local2 B).focus slots2 injective2 (fun _=>0) (bank1 B)
  have hz : dockH slots2 (fun _ : Fin 11=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots2 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input2_join B))).congr hz rfl
def joined2 := Composition.machine joined1 phase2
def budget2 (B : Nat) := budget1 B+1+cost2 B
theorem run2 (B : Nat) : Step joined2 (budget2 B) (fun _=>0) (input B) (fun _=>0) (bank2 B) :=
  (run1 B).seq (step2 B)

def slots3 : Fin 5→Fin 11 := ![3,5,6,7,8]
theorem injective3 : Function.Injective slots3 := by decide
def phase3 := RecoveryFocus.machine slots3 worker3
def bank3 (B : Nat) := install slots3 (bank2 B) (output3 B)
theorem bank3_slot (B : Nat) (j : Fin 5) : bank3 B (slots3 j)=output3 B j :=
  install_slot slots3 injective3 _ _ j
theorem bank3_other (B : Nat) (i : Fin 11) (hi : ∀ j,slots3 j≠i) : bank3 B i=bank2 B i :=
  install_other slots3 _ _ _ hi

theorem input3_join (B : Nat) : ∀ j,bank2 B (slots3 j)=input3 B j := by
  intro j
  fin_cases j
  · change bank2 B 3=input3 B 0
    change bank2 B (slots2 1)=_
    rw [bank2_slot]
    rfl
  · change bank2 B 5=input3 B 1
    rw [bank2_other B 5 (by decide)]
    rw [bank1_other B 5 (by decide)]
    rfl
  · change bank2 B 6=input3 B 2
    rw [bank2_other B 6 (by decide)]
    rw [bank1_other B 6 (by decide)]
    rfl
  · change bank2 B 7=input3 B 3
    rw [bank2_other B 7 (by decide)]
    rw [bank1_other B 7 (by decide)]
    rfl
  · change bank2 B 8=input3 B 4
    rw [bank2_other B 8 (by decide)]
    rw [bank1_other B 8 (by decide)]
    rfl
theorem step3 (B : Nat) : Step phase3 (cost3 B) (fun _=>0) (bank2 B)
    (fun _=>0) (bank3 B) := by
  have h:=(local3 B).focus slots3 injective3 (fun _=>0) (bank2 B)
  have hz : dockH slots3 (fun _ : Fin 11=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots3 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input3_join B))).congr hz rfl
def joined3 := Composition.machine joined2 phase3
def budget3 (B : Nat) := budget2 B+1+cost3 B
theorem run3 (B : Nat) : Step joined3 (budget3 B) (fun _=>0) (input B) (fun _=>0) (bank3 B) :=
  (run2 B).seq (step3 B)

def slots4 : Fin 3→Fin 11 := ![7,9,10]
theorem injective4 : Function.Injective slots4 := by decide
def phase4 := RecoveryFocus.machine slots4 worker4
def bank4 (B : Nat) := install slots4 (bank3 B) (output4 B)
theorem bank4_slot (B : Nat) (j : Fin 3) : bank4 B (slots4 j)=output4 B j :=
  install_slot slots4 injective4 _ _ j
theorem bank4_other (B : Nat) (i : Fin 11) (hi : ∀ j,slots4 j≠i) : bank4 B i=bank3 B i :=
  install_other slots4 _ _ _ hi

theorem input4_join (B : Nat) : ∀ j,bank3 B (slots4 j)=input4 B j := by
  intro j
  fin_cases j
  · change bank3 B 7=input4 B 0
    change bank3 B (slots3 3)=_
    rw [bank3_slot]
    exact output3_value B
  · change bank3 B 9=input4 B 1
    rw [bank3_other B 9 (by decide)]
    rw [bank2_other B 9 (by decide)]
    rw [bank1_other B 9 (by decide)]
    rfl
  · change bank3 B 10=input4 B 2
    rw [bank3_other B 10 (by decide)]
    rw [bank2_other B 10 (by decide)]
    rw [bank1_other B 10 (by decide)]
    rfl
theorem step4 (B : Nat) : Step phase4 (cost4 B) (fun _=>0) (bank3 B)
    (fun _=>0) (bank4 B) := by
  have h:=(local4 B).focus slots4 injective4 (fun _=>0) (bank3 B)
  have hz : dockH slots4 (fun _ : Fin 11=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    unfold dockH
    cases RecoveryFocus.pick slots4 i <;>rfl
  exact (h.congr_in hz (install_existing _ _ _ (input4_join B))).congr hz rfl
def joined4 := Composition.machine joined3 phase4
def budget4 (B : Nat) := budget3 B+1+cost4 B
theorem run4 (B : Nat) : Step joined4 (budget4 B) (fun _=>0) (input B) (fun _=>0) (bank4 B) :=
  (run3 B).seq (step4 B)

def raise : Machine 11 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some ⟨1,fun _=>none,fun i=>if i=9 then .right else .stay⟩ else none
def heads (i : Fin 11) : Nat := if i=9 then 1 else 0

theorem raise_run (A : Fin 11→List Bool) : Step raise 1 (fun _=>0) A heads A := by
  let first : Configuration 11 2 := ⟨0,fun _=>0,A⟩
  let last : Configuration 11 2 := ⟨1,heads,A⟩
  have h : step raise first=some last := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def machine := Composition.machine joined4 raise
abbrev output := bank4

theorem budget_eq (B : Nat) : budget4 B+1+1=16*B+64 := by
  simp only [budget4,budget3,budget2,budget1,cost1,cost2,cost3,cost4,
    DimensionPower.cost,WilliamsUnaryProduct.budget,pow_zero,Nat.mul_one]
  ring

theorem run (B : Nat) : Step machine (16*B+64) (fun _=>0) (input B) heads (output B) := by
  have h := (run4 B).seq (raise_run (bank4 B))
  rw [budget_eq] at h
  exact h

theorem width_template (B : Nat) : output B 9=UnaryTemplate.tape (2*B+3) := by
  have h:=bank4_slot B 1
  change output B 9=UnaryTemplate.tape (2*(B+1)+1) at h
  rw [show 2*(B+1)+1=2*B+3 by omega] at h
  exact h

theorem source_template (B : Nat) : output B 0=UnaryTemplate.tape B := by
  change bank4 B 0=_
  rw [bank4_other B 0 (by decide),bank3_other B 0 (by decide),bank2_other B 0 (by decide)]
  exact bank1_slot B 0

end
end Theorem25Completion.CycleMaskWidth
