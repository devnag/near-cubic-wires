import Proof.Assembly.Production

/-! Exact operations consumed by the packet writer's normalization kernel.
The outer list order is part of the accepted raw output.  In particular, an
addition is normalized from the REVERSED initial accumulator, and multiplication
visits the left input first and the right input second. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ6ffe03e3512f426d.Normalizer
open PCJ9eff70d512234a4c_Fixed
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary

theorem fold_append {α β : Type} (f : β → α → β) (xs ys : List α) (a : β) :
    (xs ++ ys).foldl f a = ys.foldl f (xs.foldl f a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact ih (f a x)

theorem fold_map {α β γ : Type} (f : γ → β → γ) (g : α → β)
    (xs : List α) (a : γ) :
    (xs.map g).foldl f a = xs.foldl (fun a x => f a (g x)) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact ih (f a (g x))

theorem fold_flatMap {α β γ : Type} (f : γ → β → γ) (g : α → List β)
    (xs : List α) (a : γ) :
    (xs.flatMap g).foldl f a = xs.foldl (fun a x => (g x).foldl f a) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    change (g x ++ xs.flatMap g).foldl f a = _
    rw [fold_append, ih]
    rfl

/-- This expansion is a single multiplication batch, never an expansion of the
whole row's constructor tree.  Its size is the product of the two current
normalized accumulator sizes. -/
def productBatch {α : Type} (P Q : Ring.Poly α) : Ring.Poly α :=
  P.flatMap (fun m => Q.map (fun n => m ++ n))

theorem mul_eq_norm_productBatch {α : Type} [LinearOrder α] (P Q : Ring.Poly α) :
    Ring.mul P Q = Ring.norm (productBatch P Q) := by
  unfold productBatch Ring.norm Ring.mul
  rw [fold_flatMap]
  simp only [fold_map]

end PCJ6ffe03e3512f426d.Normalizer
