import Std.Tactic

/-! Coefficient cancellation laws used by the ordinary parity scan.
This module imports no paper assumptions and introduces no execution model. -/
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PhysicalCoefficientAlgebra

variable {α : Type} [DecidableEq α]

def coefficient (needle : α) (rows : List α) (initial : Bool := false) : Bool :=
  rows.foldl (fun acc row => xor acc (decide (needle = row))) initial

@[simp] theorem coefficient_nil (needle : α) (initial : Bool) :
    coefficient needle [] initial = initial := rfl

@[simp] theorem coefficient_cons (needle row : α) (rows : List α) (initial : Bool) :
    coefficient needle (row::rows) initial =
      coefficient needle rows (xor initial (decide (needle = row))) := rfl

def toggle (row : α) (rows : List α) : List α :=
  if row ∈ rows then rows.erase row else row::rows

/-- Encoding monomials does not change cancellation coefficients, provided
its byte representation distinguishes different supports. -/
theorem coefficient_map {β : Type} [DecidableEq β]
    (encode : α → β) (hinj : Function.Injective encode)
    (needle : α) (rows : List α) (initial : Bool) :
    coefficient (encode needle) (rows.map encode) initial =
      coefficient needle rows initial := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, coefficient_cons]
    have he : decide (encode needle = encode row) = decide (needle = row) :=
      decide_eq_decide.mpr ⟨(fun h => hinj h), congrArg encode⟩
    rw [he]
    exact ih _

end PhysicalCoefficientAlgebra
