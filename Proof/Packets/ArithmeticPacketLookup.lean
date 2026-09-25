import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.PacketBankLookup

/-! Actual atom/vector lookup into the reusable left operand. The resident
source, physical index, other operand, and all reserve drivers are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticLookup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def H (countHead : Nat) (i : Fin 37) : Nat :=
  if i=28 then countHead else if i=31 ∨ i=35 then 1 else 0

def A (B R index : Nat) (left right : List (List Bool)) (source : List Bool) : Fin 37→List Bool :=
  Fin.addCases (m:=34) (n:=3) (ReusableArithmetic.state B R left right)
    (![source,ZeroPadding.pad R (CompareMachine.word index),List.replicate R false])

def countMove (move : HeadMove) : Machine 37 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some
    ⟨1,fun _=>none,fun i=>if i=28 then move else .stay⟩ else none

theorem countMove_run (move : HeadMove) (cp : Nat) (a : Fin 37→List Bool) :
    Step (countMove move) 1 (H cp) a (H (move.apply cp)) a := by
  have hs : step (countMove move) (⟨0,H cp,a⟩ : Configuration 37 2)=
      some ⟨1,H (move.apply cp),a⟩ := by
    simp only [step,countMove]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>simp [applyAction,HeadMove.apply,H]
    · rfl
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)


def slots : Fin 6→Fin 37 := ![31,34,25,28,35,36]
noncomputable def focused := RecoveryFocus.machine slots PacketBank.lookup
noncomputable def machine := Composition.machine (countMove .right)
  (Composition.machine focused (countMove .left))
def budget (R index : Nat) := PacketBank.lookupBudget R index+4

theorem A_worker (B R index : Nat) (left right : List (List Bool)) (source : List Bool) (i : Fin 30) :
    A B R index left right source ((i.castAdd 4).castAdd 3)=
      ZeroPadding.pad R (ReusableArithmetic.data B left right i) := by
  calc
    _=ReusableArithmetic.state B R left right (i.castAdd 4) := Fin.addCases_left _
    _=_ := by
      unfold ReusableArithmetic.state ReusableArithmetic.bank ReusableArithmetic.padded
      exact Fin.addCases_left _

theorem A_reserved (B R index : Nat) (left right : List (List Bool)) (source : List Bool) (i : Fin 4) :
    A B R index left right source ((i.natAdd 30).castAdd 3)=
      (![List.replicate (R+3) false,UnaryTemplate.tape R,List.replicate R true,
        List.replicate (R+3) false] : Fin 4→List Bool) i := by
  calc
    _=ReusableArithmetic.state B R left right (i.natAdd 30) := Fin.addCases_left _
    _=_ := by
      unfold ReusableArithmetic.state ReusableArithmetic.bank
      exact Fin.addCases_right _

theorem A_extra (B R index : Nat) (left right : List (List Bool)) (source : List Bool) (i : Fin 3) :
    A B R index left right source (i.natAdd 34)=
      (![source,ZeroPadding.pad R (CompareMachine.word index),List.replicate R false] : Fin 3→List Bool) i :=
  Fin.addCases_right _

theorem data_core (B : Nat) (left right : List (List Bool)) (i : Fin 24) :
    ReusableArithmetic.data B left right (i.castAdd 6)=NormalizeCold.data B [] i := by
  unfold ReusableArithmetic.data NormalizedMultiply.data
  exact Fin.addCases_left _

theorem data_extra (B : Nat) (left right : List (List Bool)) (i : Fin 6) :
    ReusableArithmetic.data B left right (i.natAdd 24)=NormalizedMultiply.extras B left right i := by
  unfold ReusableArithmetic.data NormalizedMultiply.data
  exact Fin.addCases_right _

theorem A_outside (B R index : Nat) (left right selected : List (List Bool))
    (source : List Bool) (i : Fin 37) (h25 : i≠25) (h28 : i≠28) :
    A B R index left right source i=A B R index selected right source i := by
  revert h25 h28
  refine Fin.addCases (m:=34) (n:=3) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=30) (n:=4) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=24) (n:=6) (fun l=>?_) (fun l=>?_) k
      · intro _ _
        rw [A_worker,A_worker,data_core,data_core]
      · intro hn25 hn28
        rw [A_worker,A_worker,data_extra,data_extra]
        fin_cases l
        · rfl
        · exact False.elim (hn25 rfl)
        · rfl
        · rfl
        · exact False.elim (hn28 rfl)
        · rfl
    · intro _ _
      rw [A_reserved,A_reserved]
  · intro _ _
    rw [A_extra,A_extra]


set_option maxHeartbeats 20000 in
theorem focused_run (B R index : Nat) (left right selected : List (List Bool))
    (pre post : List Bool) (hpre : pre.length=2*index*R)
    (hl : left.flatten.length≤R) (hlc : left.length+1≤R)
    (hs : selected.flatten.length≤R) (hsc : selected.length+1≤R) :
    let payload := ZeroPadding.pad R selected.flatten
    let count := ZeroPadding.pad R (CompareMachine.word selected.length)
    Step focused (PacketBank.lookupBudget R index)
      (H 1) (A B R index left right (pre++payload++count++post))
      (H 1) (A B R index selected right (pre++payload++count++post)) := by
  dsimp only
  have hsl : (ZeroPadding.pad R selected.flatten).length=R := by rw [ZeroPadding.pad_length,Nat.max_eq_left hs]
  have hscl : (ZeroPadding.pad R (CompareMachine.word selected.length)).length=R := by
    simp [CompareMachine.word,Nat.max_eq_left hsc]
  have hll : (ZeroPadding.pad R left.flatten).length=R := by rw [ZeroPadding.pad_length,Nat.max_eq_left hl]
  have hlcl : (ZeroPadding.pad R (CompareMachine.word left.length)).length=R := by
    simp [CompareMachine.word,Nat.max_eq_left hlc]
  have h := (PacketBank.lookup_run R index pre (ZeroPadding.pad R selected.flatten)
    (ZeroPadding.pad R (CompareMachine.word selected.length)) post
    (ZeroPadding.pad R left.flatten) (ZeroPadding.pad R (CompareMachine.word left.length))
    hpre hsl hscl hll hlcl).pad (![0,0,0,0,R,R] : Fin 6→Nat)
  apply PhysicalFocusBoundary.focus h slots (by decide) (H 1) (H 1) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [slots,A,PacketBank.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,
      ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,ZeroPadding.pad_zero]
    simp [ZeroPadding.pad]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [slots,A,PacketBank.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,
      ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,ZeroPadding.pad_zero]
    simp [ZeroPadding.pad]
  · intro i away
    refine ⟨rfl,?_⟩
    apply A_outside
    · intro hi;subst i;exact away 2 rfl
    · intro hi;subst i;exact away 3 rfl


theorem run (B R index : Nat) (left right selected : List (List Bool))
    (pre post : List Bool) (hpre : pre.length=2*index*R)
    (hl : left.flatten.length≤R) (hlc : left.length+1≤R)
    (hs : selected.flatten.length≤R) (hsc : selected.length+1≤R) :
    let payload := ZeroPadding.pad R selected.flatten
    let count := ZeroPadding.pad R (CompareMachine.word selected.length)
    Step machine (budget R index)
      (H 0) (A B R index left right (pre++payload++count++post))
      (H 0) (A B R index selected right (pre++payload++count++post)) := by
  dsimp only
  let source := pre++ZeroPadding.pad R selected.flatten++
    ZeroPadding.pad R (CompareMachine.word selected.length)++post
  have middle := focused_run B R index left right selected pre post hpre hl hlc hs hsc
  have first := countMove_run .right 0 (A B R index left right source)
  have last := countMove_run .left 1 (A B R index selected right source)
  have h := first.seq (middle.seq last)
  have hf : 1+1+(PacketBank.lookupBudget R index+1+1)=budget R index := by
    unfold budget;omega
  rw [hf] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticLookup
