import Proof.Foundations.SourceRegistry

/-! # Theorem 2.5 is not trivially satisfiable

A check of the Lean statement of paper Theorem 2.5 (`paper/paper.tex:794-808`, `thm:main-fixed`).
Nothing here is a source hypothesis or a proof of the theorem.

`constant_language_fails`: the target has teeth. A language that some zero-wire circuit computes
exactly (every constant language) violates the wire conclusion at every positive length, so no
degenerate language satisfies the target.
-/
namespace NearCubicWires.Theorem2_5_Nontrivial
open NearCubicWires RepairSource RepairRepresentation SourceInterfaces
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

/-- The zero-bottom symmetric circuit with a constant top. -/
def constantCircuit (n : ℕ) (value : Bool) : SymmetricThresholdCircuit n where
  bottomCount := 0
  bottom := Fin.elim0
  top := fun _ => value

theorem constantCircuit_eval (n : ℕ) (value : Bool) (x : BitInput n) :
    (constantCircuit n value).eval x = value := rfl

theorem constantCircuit_wireCount (n : ℕ) (value : Bool) :
    (constantCircuit n value).wireCount = 0 := by
  simp [constantCircuit, SymmetricThresholdCircuit.wireCount]

theorem agreement_self {n : ℕ} (f : BoolFunction n) : agreement f f = 1 := by
  unfold agreement
  have hcard : (Finset.univ.filter fun input : BitInput n => f input = f input).card =
      Fintype.card (BitInput n) := by
    simp
  rw [hcard]
  exact div_self (by positivity)

theorem wireScale_pos {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    0 < wireScale b k n := by
  unfold wireScale logScale
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  have hlog' : (0 : ℝ) < (Nat.clog 2 (n + 2) : ℝ) := by exact_mod_cast hlog
  positivity

/-- Teeth: at every positive length, a constant language has a zero-wire circuit
with full agreement, so it violates the symmetric wire conclusion for every
positive coefficient and every advantage below one half. -/
theorem constant_language_fails (gamma b : ℝ) (hgamma : gamma < 1 / 2) (hb : 0 < b)
    (n : ℕ) (hn : 1 ≤ n) (value : Bool) :
    ∃ circuit : SymmetricThresholdCircuit n,
      1 / 2 + gamma ≤ agreement circuit.eval (fun _ => value) ∧
        ¬ (wireScale b 5 n < (circuit.wireCount : ℝ)) := by
  refine ⟨constantCircuit n value, ?_, ?_⟩
  · have h : agreement (constantCircuit n value).eval (fun _ => value) = 1 := by
      have heq : (constantCircuit n value).eval = fun _ => value := by
        funext x
        exact constantCircuit_eval n value x
      rw [heq]
      exact agreement_self _
    rw [h]
    linarith
  · rw [constantCircuit_wireCount]
    have := wireScale_pos hb hn 5
    push_cast
    linarith

end NearCubicWires.Theorem2_5_Nontrivial
