import Proof.SourceAssembly.SourceRequestCurContract

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurMoment
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp
open NearCubicWires.SourceFactorSel.Count (mulM wordM mul_step word0_step read_flag)
noncomputable section

/-! ## The machine -/

def dmSl : Fin 11 → Fin 128 := ![0, 24, 9, 13, 28, 29, 30, 31, 32, 33, 5]
theorem dmSl_inj : Function.Injective dmSl := by decide
def tSl : Fin 5 → Fin 128 := ![25, 0, 26, 27, 5]
theorem tSl_inj : Function.Injective tSl := by decide

/-- Past the end: only the multiplier record `0`. -/
def endM := constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5

/-- Monomial `m < JL²`: the two digits, the two term flags, `k = 2`, multiplier `1`. -/
def bodyM :=
  Composition.machine (divmodM dmSl)
  (Composition.machine (constM [true] (7 : Fin 128) 5)
  (Composition.machine (constM [true] (11 : Fin 128) 5)
  (Composition.machine (constM [true, true] (22 : Fin 128) 5)
    (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW 1) (23 : Fin 128) 5))))

/-- **The moment cursor** (ONE fixed machine on the common layout). -/
def momentM :=
  Composition.machine (wordM false (1 : Fin 128) 24 5)
  (Composition.machine (mulM (1 : Fin 128) 24 25 5)
  (Composition.machine (testM tSl)
    (CloseoutRowsOriginalSwitch.machine endM bodyM (26 : Fin 128))))

/-! ## Its run -/

theorem hdm : ∀ j : Fin 11, 2 ≤ j.val → j.val < 10 →
    6 ≤ (dmSl j).val ∧ (dmSl j).val ≠ 23 ∧ (dmSl j).val ≠ 24 ∧ (dmSl j).val ≠ 25 ∧ (dmSl j).val ≠ 26 ∧
      (dmSl j).val ≠ 27 ∧ (dmSl j).val ≠ 7 ∧ (dmSl j).val ≠ 11 ∧ (dmSl j).val ≠ 22 ∧
      ((dmSl j).val = 9 ∨ (dmSl j).val = 13 ∨ 28 ≤ (dmSl j).val) := by decide

theorem moment_cursor : CursorRun momentM .moment := by
  intro sL sR nL nR m J JR Qm Q1 Q2 Qf S C E hm hS hC h0 h1 h2 h3 h4 h5 hscr
  have hmJ : m ≤ J * J := hm
  replace h0 : E 0 = ZeroPadding.pad Qm (List.replicate m true) := h0
  replace h1 : E 1 = ZeroPadding.pad Q1 (List.replicate J true) := h1
  replace h5 : E 5 = List.replicate C false := h5
  have hbig := sq_le_big J JR
  have hge := curBig_ge J JR
  have hJX : J ≤ (J + JR + 2) * (J + JR + 2) := by nlinarith
  have hJJX : J * J ≤ (J + JR + 2) * (J + JR + 2) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : J * (2 * J + 3) = 2 * (J * J) + 3 * J := by ring
  have hS1 : 1 ≤ S := by omega
  have hrec : ∀ q : ℚ, (CloseoutRowsEstimatorCoefficients.Product.record rhoW q).length = 13 := by
    intro q; rw [record_len]; rfl
  -- stage 1: `word J`
  set E1 := Function.update E 24 (ZeroPadding.pad S (CompareMachine.word J)) with hE1
  have s1 := word0_step (1 : Fin 128) 24 5 (by decide) (by decide) (by decide) J Q1 S C (by omega) (by omega)
    (fun _ => 0) E (fun _ _ => rfl) h1 (hscr 24 (by decide)) h5
  -- stage 2: `1^(J·J)`
  set E2 := Function.update E1 25 (ZeroPadding.pad S (List.replicate (J * J) true)) with hE2
  have s2 := mul_step (1 : Fin 128) 24 25 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    J J Q1 S S C (by rw [e1]; omega) (fun _ => 0) E1 (fun _ _ => rfl) (by simp [E1, h1]) (by simp [E1])
    (by simp [E1, hscr 25 (by decide)]) (by simp [E1, h5])
  -- stage 3: the block test `[J·J ≤ m]`
  obtain ⟨A3, s3, a26, f3, l27⟩ := test_step tSl tSl_inj (J * J) m S Qm S C (by omega) (by omega)
    (fun _ => 0) E2 (fun _ => rfl) (by simp [tSl, E2]) (by simp [tSl, E1, E2, h0])
    (by simp [tSl, E1, E2, hscr 26 (by decide)]) (by simp [tSl, E1, E2, hscr 27 (by decide)])
    (by simp [tSl, E1, E2, h5])
  have a26' : A3 26 = ZeroPadding.pad S [decide (J * J ≤ m)] := a26
  have f3' : ∀ z : Fin 128, z.val ≠ 26 → z.val ≠ 27 → A3 z = E2 z := fun z h26 h27 =>
    f3 z (fun e => h26 (by rw [← e]; rfl)) (fun e => h27 (by rw [← e]; rfl))
  have hE2 : ∀ z : Fin 128, z.val ≠ 24 → z.val ≠ 25 → E2 z = E z := by
    intro z h24 h25
    have n24 : z ≠ 24 := fun e => h24 (by rw [e]; rfl)
    have n25 : z ≠ 25 := fun e => h25 (by rw [e]; rfl)
    simp [E1, E2, Function.update_of_ne n24, Function.update_of_ne n25]
  have b3 : ∀ z : Fin 128, 6 ≤ z.val → z.val ≠ 24 → z.val ≠ 25 → z.val ≠ 26 → z.val ≠ 27 →
      A3 z = List.replicate S false := fun z h6 h24 h25 h26 h27 =>
    (f3' z h26 h27).trans ((hE2 z h24 h25).trans (hscr z h6))
  have k3 : ∀ z : Fin 128, z.val < 6 → A3 z = E z := fun z hz =>
    (f3' z (by omega) (by omega)).trans (hE2 z (by omega) (by omega))
  have fit3 : Fits S A3 := by
    have fit2 : Fits S E2 := by
      refine fits_update (fits_update (fits_init hscr) _ _ ?_) _ _ ?_
      · simp [CompareMachine.word]; omega
      · simp; omega
    refine fits_frame fit2 (fun z => z.val = 26 ∨ z.val = 27) (fun z hz => f3' z (fun e => hz (Or.inl e))
      (fun e => hz (Or.inr e))) ?_
    intro z hz
    rcases hz with hz | hz
    · have : z = 26 := Fin.ext hz
      subst this; rw [a26', pad_len S _ (by simp; omega)]
    · have : z = 27 := Fin.ext hz
      subst this; exact le_of_eq l27
  -- the two branches
  have hsum : 2 * J + 8 + 1 + (2 * (J * (2 * J + 3) + 2) + 2 + 1 + (testCost (J * J) + 1 + (30 * (J * J) + 200)))
      ≤ curCost J JR := by
    unfold testCost curCost; rw [e1]; omega
  by_cases hb : J * J ≤ m
  · -- past the end
    have hmeq : m = J * J := le_antisymm hmJ hb
    have hσ : selAt .moment sL sR nL nR J JR m = none := moment_end sL sR nL nR J JR m hb
    set E' := Function.update A3 23 (ZeroPadding.pad S (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0))
      with hE'
    have s4 := const_step (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5 (by decide)
      S C (by rw [hrec]; omega) (fun _ => 0) A3 rfl rfl (b3 23 (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [k3 5 (by decide)]; exact h5)
    have sw := CloseoutRowsOriginalSwitch.true_run endM bodyM (26 : Fin 128) s4
      (by show readTapeBit (A3 26) 0 = true; rw [a26', read_flag]; exact decide_eq_true hb)
    have hall := s1.seq (s2.seq (s3.seq sw))
    refine ⟨E', hall.enlarge ?_, ?_, ?_, ?_⟩
    · refine le_trans ?_ hsum
      rw [hrec]
      omega
    · have hk : ∀ z : Fin 128, 6 ≤ z.val → z.val < 23 → E' z = List.replicate S false := by
        intro z h6 h23
        have n23 : z ≠ 23 := fun e => by rw [e] at h23; exact absurd h23 (by decide)
        rw [hE', Function.update_of_ne n23]
        exact b3 z h6 (by omega) (by omega) (by omega) (by omega)
      rw [hσ]
      refine ⟨forall4 ?_ ?_ ?_ ?_, forall4 ?_ ?_ ?_ ?_, forall4 ?_ ?_ ?_ ?_, forall4 ?_ ?_ ?_ ?_, ?_, ?_⟩
      all_goals first
        | (show E' 23 = _; simp [hE', rhoOf])
        | (rw [hk _ (by decide) (by decide)]; first | exact (pad_ff S hS1).symm | exact (pad_zero S).symm)
    · intro j hj
      have n23 : j ≠ 23 := fun e => by rw [e] at hj; exact absurd hj (by decide)
      rw [hE', Function.update_of_ne n23]
      exact k3 j hj
    · exact fits_update fit3 23 _ (by rw [hrec]; omega)
  · -- monomial `m < J·J`
    have hlt : m < J * J := Nat.lt_of_not_le hb
    have hJ : 0 < J := by rcases Nat.eq_zero_or_pos J with h | h <;> [simp [h] at hlt; exact h]
    have hσ := moment_at sL sR nL nR J JR m hlt
    obtain ⟨A4, s4, a9, a13, f4, l4⟩ := divmod_step dmSl dmSl_inj m J Qm S S C hJ (by omega) (by omega)
      (by omega) (fun _ => 0) A3 (fun _ => rfl) (by simp [dmSl, k3 0 (by decide), h0])
      (by simp [dmSl, f3' 24 (by decide) (by decide), E2, E1])
      (by
        intro j h2 h10
        obtain ⟨g6, _, g24, g25, g26, g27, -⟩ := hdm j h2 h10
        exact b3 _ g6 g24 g25 g26 g27)
      (by simp [dmSl, k3 5 (by decide), h5])
    replace a9 : A4 9 = ZeroPadding.pad S (List.replicate (m / J) true) := a9
    replace a13 : A4 13 = ZeroPadding.pad S (List.replicate (m % J) true) := a13
    have f4' : ∀ z : Fin 128, z.val ≠ 9 → z.val ≠ 13 → z.val < 28 → A4 z = A3 z := by
      intro z h9 h13 h28
      apply f4
      intro j h2 h10 e
      obtain ⟨-, -, -, -, -, -, -, -, -, g⟩ := hdm j h2 h10
      rw [e] at g
      omega
    set A5 := Function.update A4 7 (ZeroPadding.pad S [true]) with hA5
    set A6 := Function.update A5 11 (ZeroPadding.pad S [true]) with hA6
    set A7 := Function.update A6 22 (ZeroPadding.pad S [true, true]) with hA7
    set E' := Function.update A7 23 (ZeroPadding.pad S (CloseoutRowsEstimatorCoefficients.Product.record rhoW 1))
      with hE'
    have b4 : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → z.val ≠ 9 → z.val ≠ 13 → A4 z = List.replicate S false :=
      fun z h6 h24 h9 h13 => (f4' z h9 h13 (by omega)).trans (b3 z h6 (by omega) (by omega) (by omega) (by omega))
    have l5 : A4 5 = List.replicate C false := (f4' 5 (by decide) (by decide) (by decide)).trans ((k3 5 (by decide)).trans h5)
    have c1 := const_step [true] (7 : Fin 128) 5 (by decide) S C (by simp; omega) (fun _ => 0) A4 rfl rfl
      (b4 7 (by decide) (by decide) (by decide) (by decide)) l5
    have c2 := const_step [true] (11 : Fin 128) 5 (by decide) S C (by simp; omega) (fun _ => 0) A5 rfl rfl
      (by simp [A5, b4 11 (by decide) (by decide) (by decide) (by decide)]) (by simp [A5, l5])
    have c3 := const_step [true, true] (22 : Fin 128) 5 (by decide) S C (by simp; omega) (fun _ => 0) A6 rfl rfl
      (by simp [A5, A6, b4 22 (by decide) (by decide) (by decide) (by decide)]) (by simp [A5, A6, l5])
    have c4 := const_step (CloseoutRowsEstimatorCoefficients.Product.record rhoW 1) (23 : Fin 128) 5 (by decide)
      S C (by rw [hrec]; omega) (fun _ => 0) A7 rfl rfl
      (by simp [A5, A6, A7, b4 23 (by decide) (by decide) (by decide) (by decide)]) (by simp [A5, A6, A7, l5])
    have body := s4.seq (c1.seq (c2.seq (c3.seq c4)))
    have sw := CloseoutRowsOriginalSwitch.false_run endM bodyM (26 : Fin 128) body
      (by show readTapeBit (A3 26) 0 = false; rw [a26', read_flag]; exact decide_eq_false hb)
    have hall := s1.seq (s2.seq (s3.seq sw))
    have hkeep : ∀ z : Fin 128, z.val ≠ 7 → z.val ≠ 11 → z.val ≠ 22 → z.val ≠ 23 → z.val ≠ 9 → z.val ≠ 13 →
        z.val < 24 → E' z = A3 z := by
      intro z h7 h11 h22 h23 h9 h13 h24
      have n7 : z ≠ 7 := fun e => h7 (by rw [e]; rfl)
      have n11 : z ≠ 11 := fun e => h11 (by rw [e]; rfl)
      have n22 : z ≠ 22 := fun e => h22 (by rw [e]; rfl)
      have n23 : z ≠ 23 := fun e => h23 (by rw [e]; rfl)
      rw [hE', Function.update_of_ne n23, hA7, Function.update_of_ne n22, hA6, Function.update_of_ne n11, hA5,
        Function.update_of_ne n7]
      exact f4' z h9 h13 (by omega)
    have hk : ∀ z : Fin 128, 6 ≤ z.val → z.val ≠ 7 → z.val ≠ 11 → z.val ≠ 22 → z.val ≠ 23 → z.val ≠ 9 →
        z.val ≠ 13 → z.val < 24 → E' z = List.replicate S false := fun z h6 h7 h11 h22 h23 h9 h13 h24 =>
      (hkeep z h7 h11 h22 h23 h9 h13 h24).trans (b3 z h6 (by omega) (by omega) (by omega) (by omega))
    have e9 : E' 9 = ZeroPadding.pad S (List.replicate (m / J) true) := by
      simp only [hE', hA7, hA6, hA5]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact a9
    have e13 : E' 13 = ZeroPadding.pad S (List.replicate (m % J) true) := by
      simp only [hE', hA7, hA6, hA5]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact a13
    refine ⟨E', hall.enlarge ?_, ?_, ?_, ?_⟩
    · refine le_trans ?_ hsum
      have hd : divmodCost m ≤ 30 * (J * J) + 60 := by unfold divmodCost; omega
      rw [hrec]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [hσ]
      refine ⟨forall4 ?_ ?_ ?_ ?_, forall4 ?_ ?_ ?_ ?_, forall4 ?_ ?_ ?_ ?_, forall4 ?_ ?_ ?_ ?_, ?_, ?_⟩
      · show E' 6 = _; rw [hk 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 10 = _; rw [hk 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 14 = _; rw [hk 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 18 = _; rw [hk 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 7 = _; simp [hE', hA7, hA6, hA5, facAt, fTerm]
      · show E' 11 = _; simp [hE', hA7, hA6, hA5, facAt, fTerm]
      · show E' 15 = _; rw [hk 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 19 = _; rw [hk 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 8 = _; rw [hk 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 12 = _; rw [hk 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 16 = _; rw [hk 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 20 = _; rw [hk 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_ff S hS1).symm
      · show E' 9 = _; rw [e9]; rfl
      · show E' 13 = _; rw [e13]; rfl
      · show E' 17 = _; rw [hk 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_zero S).symm
      · show E' 21 = _; rw [hk 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; exact (pad_zero S).symm
      · show E' 22 = _; simp [hE', hA7, kOf]
      · show E' 23 = _; simp [hE', rhoOf]
    · intro j hj
      rw [hkeep j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact k3 j hj
    · have fit4 : Fits S A4 := by
        refine fits_frame fit3 (fun z => z.val = 9 ∨ z.val = 13 ∨ 28 ≤ z.val) (fun z hz => f4' z
          (fun e => hz (Or.inl e)) (fun e => hz (Or.inr (Or.inl e))) (by
            have := fun e => hz (Or.inr (Or.inr e)); omega)) ?_
        intro z hz
        rcases hz with hz | hz | hz
        · have : z = 9 := Fin.ext hz
          subst this; rw [a9, pad_len S _ (by simp; have := Nat.div_le_self m J; omega)]
        · have : z = 13 := Fin.ext hz
          subst this; rw [a13, pad_len S _ (by simp; have := Nat.mod_lt m hJ; omega)]
        · by_cases h34 : z.val < 34
          · have hz' : ∃ j : Fin 11, 2 ≤ j.val ∧ j.val < 10 ∧ dmSl j = z := by
              have : z = ⟨z.val, z.isLt⟩ := rfl
              rcases (show z.val = 28 ∨ z.val = 29 ∨ z.val = 30 ∨ z.val = 31 ∨ z.val = 32 ∨ z.val = 33 by omega)
                with e | e | e | e | e | e
              · exact ⟨4, by decide, by decide, Fin.ext (by rw [e]; rfl)⟩
              · exact ⟨5, by decide, by decide, Fin.ext (by rw [e]; rfl)⟩
              · exact ⟨6, by decide, by decide, Fin.ext (by rw [e]; rfl)⟩
              · exact ⟨7, by decide, by decide, Fin.ext (by rw [e]; rfl)⟩
              · exact ⟨8, by decide, by decide, Fin.ext (by rw [e]; rfl)⟩
              · exact ⟨9, by decide, by decide, Fin.ext (by rw [e]; rfl)⟩
            obtain ⟨j, hj2, hj10, rfl⟩ := hz'
            exact le_of_eq (l4 j hj2 hj10)
          · rw [f4 z (by
              intro j h2 h10 e
              obtain ⟨-, -, -, -, -, -, -, -, -, g⟩ := hdm j h2 h10
              have hj : (dmSl j).val < 34 := (show ∀ k : Fin 11, (dmSl k).val < 34 by decide) j
              rw [e] at hj
              omega)]
            exact fit3 z (by omega)
      exact fits_update (fits_update (fits_update (fits_update fit4 7 _ (by simp; omega)) 11 _ (by simp; omega))
        22 _ (by simp; omega)) 23 _ (by rw [hrec]; omega)

end

end NearCubicWires.SourceRequest.CurMoment

