import Proof.CaseAnalysis.FinalSupplierCalls

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceFactorSel.CoefValue
open NearCubicWires RepairOrdinary

/-- A slot's factor: the term's coefficient when the slot is a term (`f = true`), else `1`. -/
def u (f : Bool) (t : ℚ) : ℚ := if f then t else 1

/-- Per-slot unary quantities (magnitude, denominator, sign count). -/
def nA (f : Bool) (t : ℚ) : ℕ := if f then t.num.natAbs else 1
def dA (f : Bool) (t : ℚ) : ℕ := if f then t.den else 1
def sA (f : Bool) (t : ℚ) : ℕ := if f then (decide (t.num < 0)).toNat else 0


theorem dA_pos (f : Bool) (t : ℚ) : 0 < dA f t := by
  unfold dA
  split
  · exact t.den_pos
  · exact Nat.one_pos

/-- A rational as sign · magnitude / denominator. -/
theorem split_rat (t : ℚ) :
    t = (-1 : ℚ) ^ ((decide (t.num < 0)).toNat) * (t.num.natAbs : ℚ) / (t.den : ℚ) := by
  have hd : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_nz
  have hn : ((t.num.natAbs : ℤ) : ℚ) = (-1 : ℚ) ^ ((decide (t.num < 0)).toNat) * (t.num : ℚ) := by
    by_cases h : t.num < 0
    · have e : (t.num.natAbs : ℤ) = -t.num := by omega
      rw [e, decide_eq_true h]
      push_cast
      norm_num
    · have e : (t.num.natAbs : ℤ) = t.num := by omega
      rw [e, decide_eq_false h]
      simp
  have hn' : (t.num.natAbs : ℚ) = (-1 : ℚ) ^ ((decide (t.num < 0)).toNat) * (t.num : ℚ) := by
    rw [← hn]
    exact (Int.cast_natCast _).symm
  rw [hn', ← mul_assoc, ← pow_add]
  have hsq : ((-1 : ℚ) ^ ((decide (t.num < 0)).toNat + (decide (t.num < 0)).toNat)) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [hsq, one_mul]
  exact (Rat.num_div_den t).symm

theorem u_split (f : Bool) (t : ℚ) :
    u f t = (-1 : ℚ) ^ (sA f t) * (nA f t : ℚ) / (dA f t : ℚ) := by
  cases f
  · simp [u, sA, nA, dA]
  · simp only [u, sA, nA, dA, if_true]
    exact split_rat t

/-- `(-1)^σ` by the parity of `σ`. -/
theorem neg_one_pow_parity (σ : ℕ) : (-1 : ℚ) ^ σ = ((if σ % 2 = 0 then 1 else -1 : ℤ) : ℚ) := by
  split
  · rename_i h
    rw [Even.neg_one_pow (Nat.even_iff.2 h)]
    rfl
  · rename_i h
    rw [Odd.neg_one_pow (Nat.odd_iff.2 (by omega))]
    rfl

/-- The reduced fraction, stated on the cofactors `a = N/g`, `c = D/g`. -/
theorem reduced_aux (σ a c g : ℕ) (hg : 0 < g) (hc : 0 < c) (hcop : Nat.Coprime a c) :
    CompetitorMonomialProducts.positive ((-1 : ℚ) ^ σ * ((a * g : ℕ) : ℚ) / ((c * g : ℕ) : ℚ)) =
        (if σ % 2 = 0 then a else 0) ∧
    CompetitorMonomialProducts.negative ((-1 : ℚ) ^ σ * ((a * g : ℕ) : ℚ) / ((c * g : ℕ) : ℚ)) =
        (if σ % 2 = 0 then 0 else a) ∧
    ((-1 : ℚ) ^ σ * ((a * g : ℕ) : ℚ) / ((c * g : ℕ) : ℚ)).den = c := by
  set s : ℤ := if σ % 2 = 0 then 1 else -1 with hs
  have hsa : s.natAbs = 1 := by
    rw [hs]
    split <;> rfl
  have hx : (-1 : ℚ) ^ σ * ((a * g : ℕ) : ℚ) / ((c * g : ℕ) : ℚ) = ((s * (a : ℤ) : ℤ) : ℚ) / ((c : ℤ) : ℚ) := by
    rw [neg_one_pow_parity σ, ← hs]
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast
    field_simp
  have hb : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  have hcp : (s * (a : ℤ)).natAbs.Coprime (c : ℤ).natAbs := by
    rw [Int.natAbs_mul, hsa, Nat.one_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    exact hcop
  have hnum := Rat.num_div_eq_of_coprime hb hcp
  have hden := Rat.den_div_eq_of_coprime hb hcp
  rw [hx]
  refine ⟨?_, ?_, ?_⟩
  · unfold CompetitorMonomialProducts.positive
    rw [hnum, hs]
    by_cases h : σ % 2 = 0
    · rw [if_pos h, if_pos h, one_mul, Int.toNat_natCast]
    · rw [if_neg h, if_neg h]
      exact Int.toNat_eq_zero.mpr (by omega)
  · unfold CompetitorMonomialProducts.negative
    rw [hnum, hs]
    by_cases h : σ % 2 = 0
    · rw [if_pos h, if_pos h]
      exact Int.toNat_eq_zero.mpr (by omega)
    · rw [if_neg h, if_neg h, neg_one_mul, neg_neg, Int.toNat_natCast]
  · exact_mod_cast hden

/-- **The reduced fraction** of `(-1)^σ · N / D`: its two sign parts and its denominator. -/
theorem reduced (σ N D : ℕ) (hD : 0 < D) :
    CompetitorMonomialProducts.positive ((-1 : ℚ) ^ σ * (N : ℚ) / (D : ℚ)) =
        (if σ % 2 = 0 then N / Nat.gcd N D else 0) ∧
    CompetitorMonomialProducts.negative ((-1 : ℚ) ^ σ * (N : ℚ) / (D : ℚ)) =
        (if σ % 2 = 0 then 0 else N / Nat.gcd N D) ∧
    ((-1 : ℚ) ^ σ * (N : ℚ) / (D : ℚ)).den = D / Nat.gcd N D := by
  have hg : 0 < Nat.gcd N D := Nat.gcd_pos_of_pos_right N hD
  have hNg : N / Nat.gcd N D * Nat.gcd N D = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N D)
  have hDg : D / Nat.gcd N D * Nat.gcd N D = D := Nat.div_mul_cancel (Nat.gcd_dvd_right N D)
  have hD' : 0 < D / Nat.gcd N D := Nat.div_pos (Nat.gcd_le_right N hD) hg
  have hcop : Nat.Coprime (N / Nat.gcd N D) (D / Nat.gcd N D) := Nat.coprime_div_gcd_div_gcd hg
  have := reduced_aux σ (N / Nat.gcd N D) (D / Nat.gcd N D) (Nat.gcd N D) hg hD' hcop
  rw [hNg, hDg] at this
  exact this

/-- The term reader's record IS the accumulator's parse shape. -/
theorem record_eq (c Qr : ℕ) (t : ℚ) :
    ZeroPadding.pad Qr (CloseoutRowsEstimatorCoefficients.Product.record c t) =
      ZeroPadding.pad Qr (frame [decide (t.num < 0)] ++ frame (SignedSortKey.binary c t.num.natAbs) ++
        frame (SignedSortKey.binary c t.den)) := rfl

end NearCubicWires.SourceFactorSel.CoefValue

