import Proof.MachineModel.CanonicalFourfoldRowProgram

/-! Mathematical window-coefficient identities factored from the historical
LevelCallee source, without importing its 17 missing executor modules. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowBinomial
open CanonicalFourfoldRowProgram SupplierWindow
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ringChoose_neg_natCast_castZMod (offset degree : ℕ) :
    ((Ring.choose (-(offset : ℤ)) degree : ℤ) : ZMod 2) =
      ((Nat.choose (offset + degree - 1) degree : ℕ) : ZMod 2) := by
  have hcoefficient : ∀ unit : ℤˣ, (((unit : ℤ) : ZMod 2)) = 1 := by
    intro unit
    rcases Int.units_eq_one_or unit with hunit | hunit <;> rw [hunit] <;> decide
  cases degree with
  | zero =>
      rw [Ring.choose_zero_right, Nat.choose_zero_right]
      norm_num
  | succ lower =>
      rw [Ring.choose_neg]
      have hcast :
          ((offset : ℤ) + ((lower + 1 : ℕ) : ℤ) - 1) =
            ((offset + (lower + 1) - 1 : ℕ) : ℤ) := by
        push_cast
        omega
      rw [hcast, Ring.choose_natCast, Units.smul_def, smul_eq_mul,
        Int.cast_mul, hcoefficient, one_mul, Int.cast_natCast]

/-- The full triangular Newton sum in `ℕ`, before reduction. -/
private theorem sum_choose_mul_choose (point target : ℕ) :
    (∑ lower ∈ Finset.range (point + 1),
        Nat.choose point lower * Nat.choose lower target) =
      Nat.choose point target * 2 ^ (point - target) := by
  by_cases htarget : target ≤ point
  · have hzero :
        (∑ lower ∈ Finset.Ico 0 target,
          Nat.choose point lower * Nat.choose lower target) = 0 := by
      apply Finset.sum_eq_zero
      intro lower hlower
      rw [Finset.mem_Ico] at hlower
      rw [Nat.choose_eq_zero_of_lt hlower.2, Nat.mul_zero]
    have hsplit :
        (∑ lower ∈ Finset.range (point + 1),
            Nat.choose point lower * Nat.choose lower target) =
          ∑ lower ∈ Finset.Ico target (point + 1),
            Nat.choose point lower * Nat.choose lower target := by
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le target)
          (by omega : target ≤ point + 1), hzero, Nat.zero_add]
    rw [hsplit, Finset.sum_Ico_eq_sum_range]
    have hlength : point + 1 - target = (point - target) + 1 := by omega
    rw [hlength]
    have hterm : ∀ index ∈ Finset.range ((point - target) + 1),
        Nat.choose point (target + index) *
            Nat.choose (target + index) target =
          Nat.choose point target * Nat.choose (point - target) index := by
      intro index _hindex
      rw [Nat.choose_mul (Nat.le_add_right target index)]
      congr 2
      omega
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Nat.sum_range_choose]
  · have hchoose : Nat.choose point target = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose, Nat.zero_mul]
    apply Finset.sum_eq_zero
    intro lower hlower
    rw [Finset.mem_range] at hlower
    rw [Nat.choose_eq_zero_of_lt (show lower < target by omega), Nat.mul_zero]

private theorem choose_mul_two_pow_castZMod (point target : ℕ) :
    ((Nat.choose point target * 2 ^ (point - target) : ℕ) : ZMod 2) =
      if point = target then 1 else 0 := by
  by_cases hequal : point = target
  · subst hequal
    rw [Nat.choose_self, Nat.sub_self, pow_zero, Nat.mul_one]
    simp
  · rw [if_neg hequal]
    by_cases htarget : target ≤ point
    · have hpositive : 0 < point - target := by omega
      obtain ⟨lower, hlower⟩ : ∃ lower, point - target = lower + 1 :=
        ⟨point - target - 1, by omega⟩
      rw [hlower, pow_succ]
      push_cast
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [htwo]
      ring
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul]
      simp

/-- **The triangular Newton coefficients of a Kronecker delta.**  Over `𝔽₂`
they are ordinary binomial coefficients: `triangularCoefficient (windowDelta
target) degree = choose degree target`. -/
theorem triangularCoefficient_windowDelta (target degree : ℕ) :
    triangularCoefficient (windowDelta target) degree =
      ((Nat.choose degree target : ℕ) : ZMod 2) := by
  induction degree using Nat.strong_induction_on with
  | _ degree inductionHypothesis =>
      rw [triangularCoefficient]
      have hinner :
          (∑ lower : Fin degree,
              (Nat.choose degree lower.val : ZMod 2) *
                triangularCoefficient (windowDelta target) lower.val) =
            ∑ lower ∈ Finset.range degree,
              ((Nat.choose degree lower * Nat.choose lower target : ℕ) :
                ZMod 2) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun lower =>
            (Nat.choose degree lower : ZMod 2) *
              triangularCoefficient (windowDelta target) lower) degree]
        apply Finset.sum_congr rfl
        intro lower hlower
        rw [Finset.mem_range] at hlower
        rw [inductionHypothesis lower hlower]
        push_cast
        ring
      rw [hinner]
      have hcast :
          (∑ lower ∈ Finset.range degree,
              ((Nat.choose degree lower * Nat.choose lower target : ℕ) :
                ZMod 2)) =
            ((∑ lower ∈ Finset.range degree,
              Nat.choose degree lower * Nat.choose lower target : ℕ) :
              ZMod 2) := by
        push_cast
        rfl
      rw [hcast]
      have htotal :
          (∑ lower ∈ Finset.range degree,
              Nat.choose degree lower * Nat.choose lower target) +
              Nat.choose degree target =
            Nat.choose degree target * 2 ^ (degree - target) := by
        rw [← sum_choose_mul_choose degree target, Finset.sum_range_succ,
          Nat.choose_self, Nat.one_mul]
      have hshift :
          ((∑ lower ∈ Finset.range degree,
              Nat.choose degree lower * Nat.choose lower target : ℕ) :
              ZMod 2) +
              ((Nat.choose degree target : ℕ) : ZMod 2) =
            if degree = target then 1 else 0 := by
        rw [← Nat.cast_add, htotal, choose_mul_two_pow_castZMod]
      have hdelta : windowDelta target degree =
          if degree = target then 1 else 0 := rfl
      rw [hdelta]
      have hsolve := hshift
      linear_combination -hsolve

/-! ### The window algebra with machine coefficients

Both scalings above are now parities of natural binomial coefficients, so the
two window constructions can be restated with coefficients
`CanonicalBinomialProgram` computes.  The restatements are equalities of the
*representation*, not merely of its `MvPolynomial` denotation: nothing in the
carried vector changes. -/

/-- Scaling by the parity of a natural number. -/
def gf2ParityScale (value : ℕ)
    (polynomial : StructuralGF2Polynomial) : StructuralGF2Polynomial :=
  if value % 2 = 0 then [] else polynomial

theorem structuralGF2Scale_natCast (value : ℕ)
    (polynomial : StructuralGF2Polynomial) :
    structuralGF2Scale ((value : ℕ) : ZMod 2) polynomial =
      gf2ParityScale value polynomial := by
  unfold structuralGF2Scale gf2ParityScale
  rw [← ZMod.natCast_mod]
  have hcases : value % 2 = 0 ∨ value % 2 = 1 := by omega
  rcases hcases with hcase | hcase <;> rw [hcase]
  · rw [if_pos (by norm_num), if_pos rfl]
  · rw [if_neg (by decide), if_neg (by decide)]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowBinomial
