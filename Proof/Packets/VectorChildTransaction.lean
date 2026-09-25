import Proof.Packets.VectorChildLookup
import Proof.Packets.VectorChildArithmetic

/-! Closed physical child-contribution transaction. Read the indexed resident
child into the left operand, multiply by the resident right delta packet, and add that term to the saved
parent accumulator. The source bank and physical child index are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildTransaction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads : Fin 39→Nat := Fin.addCases (m:=37) (n:=2) (motive:=fun _=>Nat)
  VectorChildLookup.heads (fun _=>0)
def tapes (B R index : Nat) (left right stored : List (List Bool)) (source : List Bool) : Fin 39→List Bool :=
  Fin.addCases (m:=37) (n:=2) (motive:=fun _=>List Bool) (VectorChildLookup.tapes B R index left right source)
    (![ZeroPadding.pad R stored.flatten,ZeroPadding.pad R (CompareMachine.word stored.length)])
def slots : Fin 36→Fin 39 := Fin.addCases (m:=34) (n:=2) (motive:=fun _=>Fin 39)
  (fun i=>i.castAdd 5) (![37,38])
def lookup := TapeEmbedding.machine 2 ArithmeticLookup.machine
def arithmetic := RecoveryFocus.machine slots VectorChildArithmetic.machine
def machine := Composition.machine lookup arithmetic

theorem slots_core (i : Fin 34) : slots (i.castAdd 2)=i.castAdd 5 := Fin.addCases_left i
theorem slots_saved (i : Fin 2) : slots (i.natAdd 34)=(![37,38] : Fin 2→Fin 39) i := Fin.addCases_right i

theorem slots_saved_eq (i : Fin 2) : slots (i.natAdd 34)=i.natAdd 37 := by
  rw [slots_saved];fin_cases i <;>rfl

theorem slots_val (i : Fin 36) : (slots i).val=if i.val<34 then i.val else i.val+3 := by
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [slots_core];simp only [Fin.val_castAdd,if_pos j.isLt]
  · rw [slots_saved];fin_cases j <;>rfl

theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv:=congrArg Fin.val he
  rw [slots_val,slots_val] at hv
  apply Fin.ext
  split_ifs at hv <;>omega

theorem heads_core (i : Fin 34) : heads (i.castAdd 5)=ReusableArithmetic.heads i := by
  calc
    _=VectorChildLookup.heads (i.castAdd 3) := Fin.addCases_left (i.castAdd 3)
    _=_ := by unfold VectorChildLookup.heads;exact Fin.addCases_left i

theorem tapes_core (B R index : Nat) (left right stored : List (List Bool)) (source : List Bool) (i : Fin 34) :
    tapes B R index left right stored source (i.castAdd 5)=ReusableArithmetic.state B R left right i := by
  calc
    _=VectorChildLookup.tapes B R index left right source (i.castAdd 3) := Fin.addCases_left (i.castAdd 3)
    _=_ := by unfold VectorChildLookup.tapes;exact Fin.addCases_left i

theorem tapes_middle (B R index : Nat) (left right stored : List (List Bool)) (source : List Bool) (i : Fin 3) :
    tapes B R index left right stored source ((i.natAdd 34).castAdd 2)=
      (![source,ZeroPadding.pad R (CompareMachine.word index),List.replicate R false] : Fin 3→List Bool) i := by
  unfold tapes VectorChildLookup.tapes
  simp only [Fin.addCases_left,Fin.addCases_right]

theorem selected_heads : (fun i=>heads (slots i))=VectorAccumulator.heads := by
  funext i
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [slots_core,heads_core]
    unfold VectorAccumulator.heads
    rw [Fin.addCases_left]
  · rw [slots_saved];fin_cases j <;>rfl

theorem selected_tapes (B R index : Nat) (left right stored : List (List Bool)) (source : List Bool) :
    (fun i=>tapes B R index left right stored source (slots i))=VectorAccumulator.tapes B R left right stored := by
  funext i
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [slots_core,tapes_core]
    unfold VectorAccumulator.tapes
    rw [Fin.addCases_left]
  · rw [slots_saved];fin_cases j <;>rfl

theorem dock {s fuel : Nat} {p : Machine 36 s}
    (B R index : Nat) (left right stored left' right' stored' : List (List Bool)) (source : List Bool)
    (h : Step p fuel VectorAccumulator.heads (VectorAccumulator.tapes B R left right stored)
      VectorAccumulator.heads (VectorAccumulator.tapes B R left' right' stored')) :
    Step (RecoveryFocus.machine slots p) fuel heads (tapes B R index left right stored source)
      heads (tapes B R index left' right' stored' source) := by
  apply PhysicalFocusBoundary.focus h slots slots_injective heads heads _ _
  · intro i;exact (congrFun selected_heads i).symm
  · intro i;exact (congrFun (selected_tapes B R index left right stored source) i).symm
  · intro i;exact (congrFun selected_heads i).symm
  · intro i;exact (congrFun (selected_tapes B R index left' right' stored' source) i).symm
  · intro i away
    refine ⟨rfl,?_⟩
    revert away
    refine Fin.addCases (m:=37) (n:=2) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=34) (n:=3) (fun k=>?_) (fun k=>?_) j
      · intro away;exact False.elim (away (k.castAdd 2) (slots_core k))
      · intro _;rw [tapes_middle,tapes_middle]
    · intro away;exact False.elim (away (j.natAdd 34) (slots_saved_eq j))

theorem left_lookup_heads : ArithmeticLookup.H 0=VectorChildLookup.heads := by
  funext i
  fin_cases i <;>rfl

def budget (B R index : Nat) (delta child acc : List (List Bool)) :=
  (PacketBank.lookupBudget R index+4)+1+VectorChildArithmetic.budget B R child delta acc

theorem run (B R index : Nat) (delta oldLeft child acc : List (List Bool)) (pre post : List Bool)
    (hpre : pre.length=2*index*R) (hr : VectorAccumulator.Fits R oldLeft)
    (hchild : VectorAccumulator.Fits R child)
    (hd : ∀ bits∈delta,bits.length=B) (hc : ∀ bits∈child,bits.length=B)
    (ha : ∀ bits∈acc,bits.length=B)
    (hmd : ∀ i,(ReusableArithmetic.data B child delta i).length≤R)
    (hmc : NormalizedMultiply.budget B child delta+3≤R)
    (had : ∀ i,(ReusableArithmetic.data B acc (VectorChildArithmetic.term child delta) i).length≤R)
    (hac : NormalizedAddition.budget B acc (VectorChildArithmetic.term child delta)+3≤R) :
    let source:=pre++ZeroPadding.pad R child.flatten++ZeroPadding.pad R (CompareMachine.word child.length)++post
    Step machine (budget B R index delta child acc) heads (tapes B R index oldLeft delta acc source) heads
      (tapes B R index (VectorAccumulator.answer acc (VectorChildArithmetic.term child delta))
        (VectorChildArithmetic.term child delta) (VectorAccumulator.answer acc (VectorChildArithmetic.term child delta)) source) := by
  dsimp only
  let source:=pre++ZeroPadding.pad R child.flatten++ZeroPadding.pad R (CompareMachine.word child.length)++post
  have first:=(ArithmeticLookup.run B R index oldLeft delta child pre post hpre hr.1 hr.2 hchild.1 hchild.2).embed
    (fun _ : Fin 2=>0)
    (![ZeroPadding.pad R acc.flatten,ZeroPadding.pad R (CompareMachine.word acc.length)] : Fin 2→List Bool)
  rw [left_lookup_heads] at first
  have second:=dock B R index child delta acc _ _ _ source
    (VectorChildArithmetic.run B R child delta acc hc hd ha hmd hmc had hac)
  exact first.seq second

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildTransaction
