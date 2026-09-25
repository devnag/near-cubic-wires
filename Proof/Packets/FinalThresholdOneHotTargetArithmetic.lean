import Proof.CaseAnalysis.RowsModeDeltaTarget

/-! The actual capped-target arithmetic has a runtime sign guard. A paid
copy supplies the second child operand, existing signed-decision code forms
both sums, and total borrow subtraction supplies the guarded target word.
Negative candidates are marked invalid; a zero target remains valid. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdOneHotTargetArithmetic
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 4→Fin 12 := ![2,3,4,5]
def decisionSlots : Fin 8→Fin 12 := ![0,2,3,1,6,7,8,9]
def subtractSlots : Fin 4→Fin 12 := ![6,7,10,11]
noncomputable def first := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine
noncomputable def second := RecoveryFocus.machine decisionSlots CompetitorSignedDecision.machine
noncomputable def third := RecoveryFocus.machine subtractSlots CompetitorSignedResidue.subtractProgram
noncomputable def machine := Composition.machine (Composition.machine first second) third
def input (u c parent child : Nat) : Fin 12→List Bool :=
  ![frame (binary u c),frame (binary u parent),frame (binary u child),[],[],[],[],[],[],[],[],[]]
def budget (u : Nat) := 24*u+29

theorem residue_of_le (u a b : Nat) (ha : a<2^u) (hle : b≤a) :
    CompetitorSignedResidue.residue u u a b=a-b := by
  have h : a+2^u-b=a-b+2^u := by omega
  unfold CompetitorSignedResidue.residue
  rw [h,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

theorem run (u c parent child : Nat) (hsum : c+parent<2^u) (htwice : 2*child<2^u) :
    ∃ T,Step machine (budget u) (fun _=>0) (input u c parent child) (fun _=>0) T ∧
      T 0=frame (binary u c) ∧ T 1=frame (binary u parent) ∧ T 2=frame (binary u child) ∧
      T 6=frame (binary u (c+parent)) ∧ T 7=frame (binary u (2*child)) ∧
      T 8=[decide (2*child≤c+parent)] ∧
      T 10=frame (binary u (CompetitorSignedResidue.residue u u (c+parent) (2*child))) ∧
      (2*child≤c+parent → T 10=frame (binary u (c+parent-2*child))) := by
  have copied:=Step.of_ready (RecoveryRootRound.copy_ready (binary u child) [] 0 0 (by simp))
  simp only [binary_length,List.replicate_zero,Nat.zero_max] at copied
  have firstRun:=copied.dock copySlots (by decide) (fun _=>0) (input u c parent child)
    (by intro j;rfl) (by intro j;fin_cases j <;> rfl)
  rw [dockH_existing copySlots (fun _=>0) (fun _=>0) (by intro j;rfl)] at firstRun
  let stage0:=install copySlots (input u c parent child)
    ![frame (binary u child),frame (binary u child),List.replicate (2*u+1) false,List.replicate (4*u+3) false]
  have decision:=Step.of_ready (CompetitorSignedDecision.signed_decision_run u c child child parent
    hsum (by omega))
  have secondRun:=decision.dock decisionSlots (by decide) (fun _=>0) stage0 (by intro j;rfl) (by
    intro j;fin_cases j
    · exact install_other copySlots _ _ 0 (by decide)
    · exact install_slot copySlots (by decide) _ _ 0
    · exact install_slot copySlots (by decide) _ _ 1
    · exact install_other copySlots _ _ 1 (by decide)
    all_goals exact install_other copySlots _ _ _ (by intro j;fin_cases j <;> decide))
  rw [dockH_existing decisionSlots (fun _=>0) (fun _=>0) (by intro j;rfl)] at secondRun
  let stage1:=install decisionSlots stage0 (CompetitorSignedDecision.output u c child child parent)
  obtain ⟨sub,⟨receipt,hr,rt,rh,rs⟩,sub0,sub1,sub2⟩:=
    CompetitorSignedResidue.subtract_ready u (c+parent) (2*child) hsum htwice
  have subtractRun : Step CompetitorSignedResidue.subtractProgram (4*u+4) (fun _=>0)
      ![frame (binary u (c+parent)),frame (binary u (2*child)),[],[]] (fun _=>0) sub :=
    ⟨receipt,hr,funext rh,rt,rs⟩
  have thirdRun:=subtractRun.dock subtractSlots (by decide) (fun _=>0) stage1 (by intro j;rfl) (by
    intro j;fin_cases j
    · exact install_slot decisionSlots (by decide) _ _ 4
    · change stage1 7=frame (binary u (2*child))
      have h:=install_slot decisionSlots (by decide) stage0 (CompetitorSignedDecision.output u c child child parent) 5
      change stage1 7=frame (binary u (child+child)) at h
      simpa only [show child+child=2*child by omega] using h
    all_goals
      dsimp only [stage1]
      rw [install_other decisionSlots stage0 _ _ (by intro j;fin_cases j <;> decide)]
      exact install_other copySlots _ _ _ (by intro j;fin_cases j <;> decide))
  rw [dockH_existing subtractSlots (fun _=>0) (fun _=>0) (by intro j;rfl)] at thirdRun
  have whole:=(firstRun.seq secondRun).seq thirdRun
  have cost : (8*u+8+1+(12*u+15))+1+(4*u+4)=budget u := by unfold budget;omega
  rw [cost] at whole
  let T:=install subtractSlots stage1 sub
  have target : T 10=frame (binary u (CompetitorSignedResidue.residue u u (c+parent) (2*child))) :=
    (install_slot subtractSlots (by decide) _ _ 2).trans sub2
  have kept (i : Fin 8) (hi : i=0 ∨ i=1 ∨ i=3 ∨ i=6) :
      T (decisionSlots i)=CompetitorSignedDecision.output u c child child parent i := by
    apply (install_other subtractSlots stage1 sub (decisionSlots i) ?_).trans
      (install_slot decisionSlots (by decide) _ _ i)
    rcases hi with rfl|rfl|rfl|rfl <;> intro j <;> fin_cases j <;> decide
  refine ⟨T,whole,kept 0 (by simp),kept 3 (by simp),kept 1 (by simp),?_,?_,?_,target,?_⟩
  · exact (install_slot subtractSlots (by decide) _ _ 0).trans sub0
  · exact (install_slot subtractSlots (by decide) _ _ 1).trans sub1
  · have h:=kept 6 (by simp)
    change T 8=[decide (child+child≤c+parent)] at h
    simpa only [show child+child=2*child by omega] using h
  · intro hle
    rw [target,residue_of_le u (c+parent) (2*child) hsum hle]

theorem target_option (n w parent child : Nat) :
    SupplierListPolynomial.deltaTarget? n w parent child=
      if 2*child ≤ min n w+parent then
        if min n w+parent-2*child ≤ 2*w then some (min n w+parent-2*child) else none
      else none := by
  rw [CloseoutRowsModeDeltaTarget.capped_target]
  by_cases lo : 2*child ≤ min n w+parent
  · have hi : min n w+parent ≤ 2*child+2*w ↔ min n w+parent-2*child ≤ 2*w := by omega
    simp only [lo,true_and,if_true,hi]
  · simp only [lo,false_and,if_false]

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdOneHotTargetArithmetic
