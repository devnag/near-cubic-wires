import Proof.Rows.FinalDominanceEncoder

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.ExtDecompositionBatch (Step)
open NearCubicWires.RepairOrdinary.CompetitorCountMask (mask)
open NearCubicWires.RepairSource.CloseoutFinal

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CellComparator

set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The per-cell verdict is an EQUALITY of two words -/

/-- One scanned bit pair folded into the running verdict. -/
def agree (a b old : Bool) : Bool := old && (a == b)

/-- The verdict of one low-bit-first scan of two words: they agree everywhere. -/
def decision : List Bool → List Bool → Bool → Bool
  | [], _, old => old
  | a :: ls, b :: rs, old => decision ls rs (agree a b old)
  | _ :: _, [], old => old

theorem decision_false (left right : List Bool) : decision left right false = false := by
  induction left generalizing right with
  | nil => rfl
  | cons a left ih =>
    cases right with
    | nil => rfl
    | cons b right => simpa [decision, agree] using ih right

/-- **The scan decides word equality.**  A.3.1 :1978-1979 selects the printed row whose offset
tuple EQUALS the column's residual offset tuple. -/
theorem decision_eq (left right : List Bool) (hw : left.length = right.length) :
    decision left right true = decide (left = right) := by
  induction left generalizing right with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst hr
    simp [decision]
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length = right.length := by simpa using hw
      by_cases hab : a = b
      · subst hab
        rw [decision, agree]
        simp only [Bool.true_and, beq_self_eq_true]
        rw [ih right hlen]
        simp
      · have hb : (a == b) = false := by simpa using hab
        rw [decision, agree, Bool.true_and, hb, decision_false]
        simp [hab]

/-! ## §2 The body machine: a streaming word comparator -/

def machine : Machine 3 5 where
  descriptionBits := 0
  start := Compare.scanState true
  halted := fun state => state.val == 4
  rule := fun state scanned =>
    if state.val < 2 then
      (if scanned 0 then some (Compare.action (Compare.bitState (state.val == 1)) .right none)
        else some (Compare.action 4 .right (some (state.val == 1))))
    else if state.val < 4 then
      some (Compare.action
        (Compare.scanState (agree (scanned 0) (scanned 1) (state.val == 3))) .right none)
    else none

theorem marker_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool)
    (old : Bool) (hr : readTapeBit left leftHead = true) :
    step machine (Compare.config (Compare.scanState old) left right leftHead rightHead output) =
      some (Compare.config (Compare.bitState old) left right (leftHead + 1) (rightHead + 1)
        output) := by
  cases old <;>
    simp [step, machine, Compare.scanState, Compare.bitState, Compare.config,
      Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, Compare.action, HeadMove.apply])

theorem bit_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool)
    (old a b : Bool) (hl : readTapeBit left leftHead = a) (hr : readTapeBit right rightHead = b) :
    step machine (Compare.config (Compare.bitState old) left right leftHead rightHead output) =
      some (Compare.config (Compare.scanState (agree a b old)) left right (leftHead + 1)
        (rightHead + 1) output) := by
  cases old <;>
    simp [step, machine, Compare.scanState, Compare.bitState, Compare.config,
      Configuration.scanned, hl, hr] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, Compare.action, HeadMove.apply])

theorem finish_step (left right : List Bool) (leftHead rightHead : ℕ) (output : List Bool)
    (old : Bool) (hr : readTapeBit left leftHead = false) :
    step machine (Compare.config (Compare.scanState old) left right leftHead rightHead output) =
      some (Compare.config 4 left right (leftHead + 1) (rightHead + 1) (output ++ [old])) := by
  cases old <;>
    simp [step, machine, Compare.scanState, Compare.config, Configuration.scanned, hr] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;>
        simp [applyAction, Compare.action, HeadMove.apply, Streaming.write_append])

theorem scan_prefix (preLeft preRight left right tailLeft tailRight output : List Bool)
    (old : Bool) (hw : left.length = right.length) :
    Prefix machine
      ((preLeft ++ frame left ++ tailLeft).length + (preRight ++ frame right ++ tailRight).length +
        output.length + 1)
      (2 * left.length + 1)
      (Compare.config (Compare.scanState old) (preLeft ++ frame left ++ tailLeft)
        (preRight ++ frame right ++ tailRight) preLeft.length preRight.length output)
      (Compare.config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length + 1) (preRight.length + 2 * right.length + 1)
        (output ++ [decision left right old])) := by
  induction left generalizing preLeft preRight right old with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    have hread := Streaming.read_append preLeft tailLeft false
    have hfnil : frame ([] : List Bool) = [false] := rfl
    have hp := finish_step (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
      preLeft.length preRight.length output old
      (by rw [hfnil, List.append_assoc]; exact hread)
    refine Prefix.step (by simp) (by cases old <;> rfl) hp ?_
    simpa [decision] using Prefix.refl
      (Compare.config 4 (preLeft ++ frame [] ++ tailLeft) (preRight ++ frame [] ++ tailRight)
        (preLeft.length + 1) (preRight.length + 1) (output ++ [old])) (by simp; omega)
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length = right.length := by simpa using hw
      have hfc : ∀ (x : Bool) (xs : List Bool),
          frame (x :: xs) = true :: x :: frame xs := fun _ _ => rfl
      let lhs := preLeft ++ frame (a :: left) ++ tailLeft
      let rhs := preRight ++ frame (b :: right) ++ tailRight
      let space := lhs.length + rhs.length + output.length + 1
      have ht : Prefix machine space (2 * left.length + 1)
          (Compare.config (Compare.scanState (agree a b old)) lhs rhs (preLeft.length + 2)
            (preRight.length + 2) output)
          (Compare.config 4 lhs rhs (preLeft.length + 2 * (a :: left).length + 1)
            (preRight.length + 2 * (b :: right).length + 1)
            (output ++ [decision (a :: left) (b :: right) old])) := by
        have hi := ih (preLeft ++ [true, a]) (preRight ++ [true, b]) right (agree a b old) hlen
        convert hi using 1 <;>
          simp [lhs, rhs, space, hfc, decision, agree, List.append_assoc, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hread : readTapeBit lhs preLeft.length = true := by
        show readTapeBit (preLeft ++ frame (a :: left) ++ tailLeft) preLeft.length = true
        rw [hfc, List.append_assoc]
        exact Streaming.read_append preLeft (a :: (frame left ++ tailLeft)) true
      have hl : readTapeBit lhs (preLeft.length + 1) = a := by
        show readTapeBit (preLeft ++ frame (a :: left) ++ tailLeft) (preLeft.length + 1) = a
        have h := Streaming.read_append (preLeft ++ [true]) (frame left ++ tailLeft) a
        have hlen1 : (preLeft ++ [true]).length = preLeft.length + 1 := by simp
        rw [hlen1, List.append_assoc] at h
        rw [hfc, List.append_assoc]
        exact h
      have hrb : readTapeBit rhs (preRight.length + 1) = b := by
        show readTapeBit (preRight ++ frame (b :: right) ++ tailRight) (preRight.length + 1) = b
        have h := Streaming.read_append (preRight ++ [true]) (frame right ++ tailRight) b
        have hlen1 : (preRight ++ [true]).length = preRight.length + 1 := by simp
        rw [hlen1, List.append_assoc] at h
        rw [hfc, List.append_assoc]
        exact h
      have hbit := bit_step lhs rhs (preLeft.length + 1) (preRight.length + 1) output old a b hl hrb
      have hp := Prefix.step
        (by simp [space] :
          (Compare.config (Compare.bitState old) lhs rhs (preLeft.length + 1)
            (preRight.length + 1) output).tapeCells ≤ space)
        (by cases old <;> rfl) hbit (by simpa [Nat.add_assoc] using ht)
      have hstart := Prefix.step
        (by simp [space] :
          (Compare.config (Compare.scanState old) lhs rhs preLeft.length preRight.length
            output).tapeCells ≤ space)
        (by cases old <;> rfl)
        (marker_step lhs rhs preLeft.length preRight.length output old hread) hp
      convert hstart using 1 <;> simp [lhs, rhs, Nat.mul_add, Nat.add_assoc]

theorem equal_run (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom machine (2 * left.length + 1)
        (Compare.config machine.start (preLeft ++ frame left ++ tailLeft)
          (preRight ++ frame right ++ tailRight) preLeft.length preRight.length output) = some r ∧
      r.final = Compare.config 4 (preLeft ++ frame left ++ tailLeft)
        (preRight ++ frame right ++ tailRight) (preLeft.length + 2 * left.length + 1)
        (preRight.length + 2 * right.length + 1) (output ++ [decide (left = right)]) ∧
      r.steps = 2 * left.length + 1 := by
  have hp := scan_prefix preLeft preRight left right tailLeft tailRight output true hw
  obtain ⟨r, hr, hf, hs, -⟩ := hp.run (by rfl) (by simp; omega)
  exact ⟨r, hr, by simpa only [decision_eq left right hw] using hf, hs⟩

/-! ## §3 The two words of one cell, and the tapes that stream them -/

section Words

noncomputable section

/-! ## §4 The streamed tapes and the loop driver's per-round source -/

/-! ## §5 The scan, realised -/

end

end Words


end NearCubicWires.RepairSource.CloseoutFinal.C10CellComparator
