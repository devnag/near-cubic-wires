import Proof.SourceAssembly.SourceRequestSelCostFront

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.SourceFactorSel.CoefValue (nA dA sA)
noncomputable section

/-! ## Unary-dimension budget of a decoded binary word -/

theorem ub_bin (c n : Nat) (hn : n < 2 ^ c) :
    SourceFactorSel.CoefAcc.ub (SignedSortKey.binary c n) = 24 * (n + 1) * (c + 1) + 2 * n + 9 := by
  unfold SourceFactorSel.CoefAcc.ub RepairSource.RecoveryProjectionDimension.budget
    RepairSource.ProjectionNormalization.Unary.budget
  rw [SignedSortKey.binary_value c n hn, SignedSortKey.binary_length]

theorem ub_flag (s : Bool) : SourceFactorSel.CoefAcc.ub [s] ≤ 107 := by
  unfold SourceFactorSel.CoefAcc.ub RepairSource.RecoveryProjectionDimension.budget
    RepairSource.ProjectionNormalization.Unary.budget
  rw [SourceFactorSel.CoefAcc.value_flag]
  have := Bool.toNat_le s
  simp only [List.length_singleton]
  have e : 24 * (s.toNat + 1) * (1 + 1) = 48 * s.toNat + 48 := by ring
  omega

/-! ## Powers of `W` -/

structure Pows (W : Nat) : Prop where
  w1 : 4 ≤ W
  p1 : W ≤ W ^ 2
  p2 : W ^ 2 ≤ W ^ 3
  p3 : W ^ 3 ≤ W ^ 4
  p4 : W ^ 4 ≤ W ^ 5
  p5 : W ^ 5 ≤ W ^ 10
  e2 : W * W = W ^ 2
  e3 : W * W ^ 2 = W ^ 3
  e4 : W * W ^ 3 = W ^ 4
  e5 : W * W ^ 4 = W ^ 5
  e10 : W ^ 5 * W ^ 5 = W ^ 10

theorem pows (W : Nat) (h : 4 ≤ W) : Pows W where
  w1 := h
  p1 := by calc W = W ^ 1 := (pow_one W).symm
             _ ≤ W ^ 2 := Nat.pow_le_pow_right (by omega) (by decide)
  p2 := Nat.pow_le_pow_right (by omega) (by decide)
  p3 := Nat.pow_le_pow_right (by omega) (by decide)
  p4 := Nat.pow_le_pow_right (by omega) (by decide)
  p5 := Nat.pow_le_pow_right (by omega) (by decide)
  e2 := by ring
  e3 := by ring
  e4 := by ring
  e5 := by ring
  e10 := by ring

/-! ## One factor's accumulation, or its skip -/

theorem accCost_le (s : Bool) (n d c Na Da sa W : Nat) (hW : Pows W) (hn : n < 2 ^ c) (hd : d < 2 ^ c)
    (hnW : n ≤ W) (hdW : d ≤ W) (hcW : c ≤ W) (hNa : Na ≤ 3 * W ^ 3) (hDa : Da ≤ 3 * W ^ 3) (hsa : sa ≤ 5) :
    SourceFactorSel.CoefAcc.accCost s n d c Na Da sa ≤ 500 * W ^ 4 := by
  obtain ⟨w1, p1, p2, p3, p4, p5, e2, e3, e4, e5, e10⟩ := hW
  unfold SourceFactorSel.CoefAcc.accCost SourceFactorSel.CoefAcc.parseCost
  rw [ub_bin c n hn, ub_bin c d hd]
  have u1 := ub_flag s
  have hs := Bool.toNat_le s
  have a1 : Na * (2 * n + 3) ≤ 15 * W ^ 4 := by
    calc Na * (2 * n + 3) ≤ (3 * W ^ 3) * (5 * W) := Nat.mul_le_mul hNa (by omega)
      _ = 15 * (W * W ^ 3) := by ring
      _ = 15 * W ^ 4 := by rw [e4]
  have a2 : Da * (2 * d + 3) ≤ 15 * W ^ 4 := by
    calc Da * (2 * d + 3) ≤ (3 * W ^ 3) * (5 * W) := Nat.mul_le_mul hDa (by omega)
      _ = 15 * (W * W ^ 3) := by ring
      _ = 15 * W ^ 4 := by rw [e4]
  have b1 : 24 * (n + 1) * (c + 1) ≤ 96 * W ^ 2 := by
    calc 24 * (n + 1) * (c + 1) ≤ 24 * (2 * W) * (2 * W) := Nat.mul_le_mul (Nat.mul_le_mul_left 24 (by omega)) (by omega)
      _ = 96 * (W * W) := by ring
      _ = 96 * W ^ 2 := by rw [e2]
  have b2 : 24 * (d + 1) * (c + 1) ≤ 96 * W ^ 2 := by
    calc 24 * (d + 1) * (c + 1) ≤ 24 * (2 * W) * (2 * W) := Nat.mul_le_mul (Nat.mul_le_mul_left 24 (by omega)) (by omega)
      _ = 96 * (W * W) := by ring
      _ = 96 * W ^ 2 := by rw [e2]
  omega

theorem accSwCost_le (f s : Bool) (n d c Na Da sa W : Nat) (hW : Pows W)
    (hf : f = true → n < 2 ^ c ∧ d < 2 ^ c ∧ n ≤ W ∧ d ≤ W) (hcW : c ≤ W)
    (hNa : Na ≤ 3 * W ^ 3) (hDa : Da ≤ 3 * W ^ 3) (hsa : sa ≤ 5) :
    SourceFactorSel.CoefBin.accSwCost f s n d c Na Da sa ≤ 502 * W ^ 4 := by
  have hW' := hW
  obtain ⟨w1, p1, p2, p3, p4, p5, e2, e3, e4, e5, e10⟩ := hW'
  unfold SourceFactorSel.CoefBin.accSwCost
  cases f
  · simp only [Bool.false_eq_true, if_false, SourceFactorSel.CoefBin.skipCost]
    omega
  · simp only [if_true]
    obtain ⟨h1, h2, h3, h4⟩ := hf rfl
    have := accCost_le s n d c Na Da sa W hW h1 h2 h3 h4 hcW hNa hDa hsa
    omega

/-! ## Division, sign, emission -/

theorem countBin_le (x B : Nat) (hx : x ≤ B) : CloseoutRowsCountBinary.budget x ≤ 16 * (B * B) + 72 * B + 36 := by
  unfold CloseoutRowsCountBinary.budget
  have h1 : x ^ 2 ≤ B * B := by rw [sq]; exact Nat.mul_le_mul hx hx
  omega

theorem tobin_le (x S W : Nat) (hW : Pows W) (hx : x ≤ 6 * W ^ 5) (hS : S ≤ 6 * W ^ 5) :
    SourceFactorSel.CoefBin.tobinCost x S ≤ 1100 * W ^ 10 := by
  obtain ⟨w1, p1, p2, p3, p4, p5, e2, e3, e4, e5, e10⟩ := hW
  unfold SourceFactorSel.CoefBin.tobinCost
  have h1 := countBin_le x (6 * W ^ 5) hx
  have h2 : 6 * W ^ 5 * (6 * W ^ 5) = 36 * W ^ 10 := by rw [← e10]; ring
  omega

theorem divideCost_le (N D4 K W : Nat) (hW : Pows W) (hN : N ≤ 3 * W ^ 4) (hD : D4 ≤ 3 * W ^ 4) (hK : K ≤ W) :
    SourceFactorSel.CoefReduce.divideCost N D4 K ≤ 6000 * W ^ 10 := by
  have hW' := hW
  obtain ⟨w1, p1, p2, p3, p4, p5, e2, e3, e4, e5, e10⟩ := hW'
  unfold SourceFactorSel.CoefReduce.divideCost SourceFactorSel.CoefPrim.gcdCost
  have hP : D4 * K ≤ 3 * W ^ 5 := by
    calc D4 * K ≤ (3 * W ^ 4) * W := Nat.mul_le_mul hD hK
      _ = 3 * (W * W ^ 4) := by ring
      _ = 3 * W ^ 5 := by rw [e5]
  have hS : N + D4 * K ≤ 6 * W ^ 5 := by omega
  have hm : D4 * (2 * K + 3) ≤ 15 * W ^ 5 := by
    calc D4 * (2 * K + 3) ≤ (3 * W ^ 4) * (5 * W) := Nat.mul_le_mul hD (by omega)
      _ = 15 * (W * W ^ 4) := by ring
      _ = 15 * W ^ 5 := by rw [e5]
  have t1 := tobin_le N (N + D4 * K) W hW (by omega) hS
  have t2 := tobin_le (D4 * K) (N + D4 * K) W hW (by omega) hS
  have hg : Nat.gcd N (D4 * K) ≤ N + D4 * K := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, Nat.gcd_zero_left]; omega
    · have := Nat.gcd_le_left (D4 * K) h0; omega
  have hg2 : Nat.gcd N (D4 * K) < 2 ^ (N + D4 * K) := Nat.lt_of_le_of_lt hg (Nat.lt_two_pow_self)
  rw [ub_bin _ _ hg2]
  have g1 : 24 * (Nat.gcd N (D4 * K) + 1) * (N + D4 * K + 1) ≤ 24 * (7 * W ^ 5) * (7 * W ^ 5) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 24 (by omega)) (by omega)
  have g2 : 24 * (7 * W ^ 5) * (7 * W ^ 5) = 1176 * W ^ 10 := by rw [← e10]; ring
  have g3 : (N + D4 * K + 1) * (32 * (N + D4 * K) + 40) ≤ (7 * W ^ 5) * (232 * W ^ 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have g4 : (7 * W ^ 5) * (232 * W ^ 5) = 1624 * W ^ 10 := by rw [← e10]; ring
  omega

theorem signCost_le (σ M' W : Nat) (hW : Pows W) (hσ : σ ≤ 5) (hM : M' ≤ 3 * W ^ 4) :
    SourceFactorSel.CoefReduce.signCost σ M' ≤ 200 * W ^ 4 := by
  obtain ⟨w1, p1, p2, p3, p4, p5, e2, e3, e4, e5, e10⟩ := hW
  unfold SourceFactorSel.CoefReduce.signCost
  have ht : (UnaryTemplate.tape 2).length ≤ 10 := by decide
  have hmin := Nat.min_le_left σ (σ / 2 + (σ / 2 + 0))
  omega

theorem emitCost_le (b p n d W : Nat) (hW : Pows W) (hb : b ≤ W) (hp : p ≤ 6 * W ^ 5) (hn : n ≤ 6 * W ^ 5)
    (hd : d ≤ 6 * W ^ 5) : SourceFactorSel.CoefReduce.emitCost b p n d ≤ 3500 * W ^ 10 := by
  have hW' := hW
  obtain ⟨w1, p1, p2, p3, p4, p5, e2, e3, e4, e5, e10⟩ := hW'
  unfold SourceFactorSel.CoefReduce.emitCost
  have hS : b + (b + 0) + 2 ≤ 6 * W ^ 5 := by omega
  have t1 := tobin_le p _ W hW hp hS
  have t2 := tobin_le n _ W hW hn hS
  have t3 := tobin_le d _ W hW hd hS
  have hl : [true, true].length = 2 := rfl
  omega

/-! ## The whole coefficient stage -/

theorem nA_le' (f : Bool) (t : ℚ) (W : Nat) (hW : 1 ≤ W) (h : f = true → t.num.natAbs < W) : nA f t ≤ W :=
  SourceFactorSel.Coef.nA_le f t W hW h

theorem dA_le' (f : Bool) (t : ℚ) (W : Nat) (hW : 1 ≤ W) (h : f = true → t.den < W) : dA f t ≤ W :=
  SourceFactorSel.Coef.dA_le f t W hW h

/-- **The coefficient stage's cost** at the value bound `W`. -/
theorem coefRCost_le (cw K b W : Nat) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) (hW4 : 4 ≤ W)
    (hcw : cw ≤ W) (hK : K ≤ W) (hb : b ≤ W)
    (hrb : rho.num.natAbs < 2 ^ SourceRequest.CurContract.rhoW ∧ rho.den < 2 ^ SourceRequest.CurContract.rhoW)
    (hv : ∀ i, f i = true → (t i).num.natAbs < W ∧ (t i).den < W)
    (hbits : ∀ i, f i = true → (t i).num.natAbs < 2 ^ cw ∧ (t i).den < 2 ^ cw) :
    SourceFactorSel.CoefR.coefRCost cw SourceRequest.CurContract.rhoW K b rho f t ≤ 20000 * W ^ 10 := by
  have hW := pows W hW4
  have hW' := hW
  obtain ⟨w1, p1, p2, p3, p4, p5, e2, e3, e4, e5, e10⟩ := hW'
  have r4 : 2 ^ SourceRequest.CurContract.rhoW = 4 := rfl
  rw [r4] at hrb
  -- the factor values
  have n0 := nA_le' (f 0) (t 0) W (by omega) (fun h => (hv 0 h).1)
  have n1 := nA_le' (f 1) (t 1) W (by omega) (fun h => (hv 1 h).1)
  have n2 := nA_le' (f 2) (t 2) W (by omega) (fun h => (hv 2 h).1)
  have n3 := nA_le' (f 3) (t 3) W (by omega) (fun h => (hv 3 h).1)
  have d0 := dA_le' (f 0) (t 0) W (by omega) (fun h => (hv 0 h).2)
  have d1 := dA_le' (f 1) (t 1) W (by omega) (fun h => (hv 1 h).2)
  have d2 := dA_le' (f 2) (t 2) W (by omega) (fun h => (hv 2 h).2)
  have d3 := dA_le' (f 3) (t 3) W (by omega) (fun h => (hv 3 h).2)
  have s0 := SourceFactorSel.Coef.sA_le (f 0) (t 0)
  have s1 := SourceFactorSel.Coef.sA_le (f 1) (t 1)
  have s2 := SourceFactorSel.Coef.sA_le (f 2) (t 2)
  have s3 := SourceFactorSel.Coef.sA_le (f 3) (t 3)
  -- the accumulated products
  have R0 : SourceFactorSel.CoefR.RN0 rho ≤ 3 := by unfold SourceFactorSel.CoefR.RN0; omega
  have D0 : SourceFactorSel.CoefR.RD0 rho ≤ 3 := by unfold SourceFactorSel.CoefR.RD0; omega
  have R1 : SourceFactorSel.CoefR.RN1 rho f t ≤ 3 * W := by
    unfold SourceFactorSel.CoefR.RN1; exact Nat.mul_le_mul R0 n0
  have R2 : SourceFactorSel.CoefR.RN2 rho f t ≤ 3 * W ^ 2 := by
    unfold SourceFactorSel.CoefR.RN2
    calc SourceFactorSel.CoefR.RN1 rho f t * nA (f 1) (t 1) ≤ (3 * W) * W := Nat.mul_le_mul R1 n1
      _ = 3 * (W * W) := by ring
      _ = 3 * W ^ 2 := by rw [e2]
  have R3 : SourceFactorSel.CoefR.RN3 rho f t ≤ 3 * W ^ 3 := by
    unfold SourceFactorSel.CoefR.RN3
    calc SourceFactorSel.CoefR.RN2 rho f t * nA (f 2) (t 2) ≤ (3 * W ^ 2) * W := Nat.mul_le_mul R2 n2
      _ = 3 * (W * W ^ 2) := by ring
      _ = 3 * W ^ 3 := by rw [e3]
  have RN : SourceFactorSel.CoefR.numR rho f t ≤ 3 * W ^ 4 := by
    unfold SourceFactorSel.CoefR.numR
    calc SourceFactorSel.CoefR.RN3 rho f t * nA (f 3) (t 3) ≤ (3 * W ^ 3) * W := Nat.mul_le_mul R3 n3
      _ = 3 * (W * W ^ 3) := by ring
      _ = 3 * W ^ 4 := by rw [e4]
  have D1 : SourceFactorSel.CoefR.RD1 rho f t ≤ 3 * W := by
    unfold SourceFactorSel.CoefR.RD1; exact Nat.mul_le_mul D0 d0
  have D2 : SourceFactorSel.CoefR.RD2 rho f t ≤ 3 * W ^ 2 := by
    unfold SourceFactorSel.CoefR.RD2
    calc SourceFactorSel.CoefR.RD1 rho f t * dA (f 1) (t 1) ≤ (3 * W) * W := Nat.mul_le_mul D1 d1
      _ = 3 * (W * W) := by ring
      _ = 3 * W ^ 2 := by rw [e2]
  have D3 : SourceFactorSel.CoefR.RD3 rho f t ≤ 3 * W ^ 3 := by
    unfold SourceFactorSel.CoefR.RD3
    calc SourceFactorSel.CoefR.RD2 rho f t * dA (f 2) (t 2) ≤ (3 * W ^ 2) * W := Nat.mul_le_mul D2 d2
      _ = 3 * (W * W ^ 2) := by ring
      _ = 3 * W ^ 3 := by rw [e3]
  have DN : SourceFactorSel.CoefR.denR rho f t ≤ 3 * W ^ 4 := by
    unfold SourceFactorSel.CoefR.denR
    calc SourceFactorSel.CoefR.RD3 rho f t * dA (f 3) (t 3) ≤ (3 * W ^ 3) * W := Nat.mul_le_mul D3 d3
      _ = 3 * (W * W ^ 3) := by ring
      _ = 3 * W ^ 4 := by rw [e4]
  have S0 : SourceFactorSel.CoefR.RS0 rho ≤ 1 := by
    unfold SourceFactorSel.CoefR.RS0; have := Bool.toNat_le (decide (rho.num < 0)); omega
  have S1 : SourceFactorSel.CoefR.RS1 rho f t ≤ 2 := by unfold SourceFactorSel.CoefR.RS1; omega
  have S2 : SourceFactorSel.CoefR.RS2 rho f t ≤ 3 := by unfold SourceFactorSel.CoefR.RS2; omega
  have S3 : SourceFactorSel.CoefR.RS3 rho f t ≤ 4 := by unfold SourceFactorSel.CoefR.RS3; omega
  have SG : SourceFactorSel.CoefR.sgnR rho f t ≤ 5 := by unfold SourceFactorSel.CoefR.sgnR; omega
  -- each factor's (accumulate | skip)
  have hacc : ∀ (i : Fin 4) (Na Da sa : Nat), Na ≤ 3 * W ^ 3 → Da ≤ 3 * W ^ 3 → sa ≤ 5 →
      SourceFactorSel.CoefBin.accSwCost (f i) (SourceFactorSel.Coef.sS (f i) (t i)) (SourceFactorSel.Coef.nS (f i) (t i))
        (SourceFactorSel.Coef.dS (f i) (t i)) cw Na Da sa ≤ 502 * W ^ 4 := by
    intro i Na Da sa hNa hDa hsa
    refine accSwCost_le _ _ _ _ _ _ _ _ W hW (fun hf => ?_) hcw hNa hDa hsa
    have e1 : SourceFactorSel.Coef.nS (f i) (t i) = (t i).num.natAbs := by simp [SourceFactorSel.Coef.nS, hf]
    have e2 : SourceFactorSel.Coef.dS (f i) (t i) = (t i).den := by simp [SourceFactorSel.Coef.dS, hf]
    rw [e1, e2]
    exact ⟨(hbits i hf).1, (hbits i hf).2, (hv i hf).1.le, (hv i hf).2.le⟩
  have a0 := hacc 0 (SourceFactorSel.CoefR.RN0 rho) (SourceFactorSel.CoefR.RD0 rho) (SourceFactorSel.CoefR.RS0 rho)
    (by omega) (by omega) (by omega)
  have a1 := hacc 1 (SourceFactorSel.CoefR.RN1 rho f t) (SourceFactorSel.CoefR.RD1 rho f t) (SourceFactorSel.CoefR.RS1 rho f t)
    (by omega) (by omega) (by omega)
  have a2 := hacc 2 (SourceFactorSel.CoefR.RN2 rho f t) (SourceFactorSel.CoefR.RD2 rho f t) (SourceFactorSel.CoefR.RS2 rho f t)
    (by omega) (by omega) (by omega)
  have a3 := hacc 3 (SourceFactorSel.CoefR.RN3 rho f t) (SourceFactorSel.CoefR.RD3 rho f t) (SourceFactorSel.CoefR.RS3 rho f t)
    R3 D3 (by omega)
  -- the multiplier's accumulation
  have am := accCost_le (decide (rho.num < 0)) rho.num.natAbs rho.den SourceRequest.CurContract.rhoW 1 1 0 W hW
    (by rw [r4]; exact hrb.1) (by rw [r4]; exact hrb.2) (by omega) (by omega) (by show 2 ≤ W; omega) (by omega)
    (by omega) (by omega)
  -- division, sign, emission
  have dv := divideCost_le (SourceFactorSel.CoefR.numR rho f t) (SourceFactorSel.CoefR.denR rho f t) K W hW RN DN hK
  have hq : SourceFactorSel.CoefR.numR rho f t / SourceFactorSel.CoefR.gcdR K rho f t ≤ 3 * W ^ 4 :=
    (Nat.div_le_self _ _).trans RN
  have sg := signCost_le (SourceFactorSel.CoefR.sgnR rho f t) _ W hW SG hq
  have hPos : SourceFactorSel.CoefR.posR K rho f t ≤ 6 * W ^ 5 := by
    unfold SourceFactorSel.CoefR.posR; split <;> omega
  have hNeg : SourceFactorSel.CoefR.negR K rho f t ≤ 6 * W ^ 5 := by
    unfold SourceFactorSel.CoefR.negR; split <;> omega
  have hDn : SourceFactorSel.CoefR.dnR K rho f t ≤ 6 * W ^ 5 := by
    unfold SourceFactorSel.CoefR.dnR
    have h1 : SourceFactorSel.CoefR.denR rho f t * K ≤ 3 * W ^ 5 := by
      calc SourceFactorSel.CoefR.denR rho f t * K ≤ (3 * W ^ 4) * W := Nat.mul_le_mul DN hK
        _ = 3 * (W * W ^ 4) := by ring
        _ = 3 * W ^ 5 := by rw [e5]
    have := Nat.div_le_self (SourceFactorSel.CoefR.denR rho f t * K) (SourceFactorSel.CoefR.gcdR K rho f t)
    omega
  have em := emitCost_le b _ _ _ W hW hb hPos hNeg hDn
  unfold SourceFactorSel.CoefR.coefRCost
  omega

end
end NearCubicWires.SourceRequest.SelLocal

