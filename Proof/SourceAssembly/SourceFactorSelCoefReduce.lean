import Proof.SourceAssembly.SourceFactorSelCoefBin

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefReduce
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim NearCubicWires.SourceFactorSel.CoefAcc NearCubicWires.SourceFactorSel.CoefBin
noncomputable section

/-! ## Docked primitives and frame lemmas -/

theorem dz {t u s : Nat} {p : Machine t s} {n : Nat} {E E' : Fin t → List Bool}
    (h : Step p n (fun _ => 0) E (fun _ => 0) E') (sl : Fin t → Fin u) (hsl : Function.Injective sl)
    (H : Fin u → Nat) (A : Fin u → List Bool) (hH : ∀ j, H (sl j) = 0) (hA : ∀ j, A (sl j) = E j) :
    Step (RecoveryFocus.machine sl p) n H A H (install sl A E') := by
  have d := h.dock sl hsl H A (fun j => hH j) hA
  rwa [dockH_existing sl H (fun _ => 0) hH] at d

theorem gcd_step {U : Nat} (sl : Fin 7 → Fin U) (hsl : Function.Injective sl) (w a b Qa Qb S : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qa (frame (binary w a)))
    (h1 : A (sl 1) = ZeroPadding.pad Qb (frame (binary w b)))
    (hs : ∀ j : Fin 7, 2 ≤ j.val → A (sl j) = List.replicate S false) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl gcdM) (gcdCost w a b) H A H A' ∧
      A' (sl 2) = ZeroPadding.pad S (frame (binary w (Nat.gcd a b))) ∧ (∀ x, (∀ j, sl j ≠ x) → A' x = A x) := by
  obtain ⟨E', hs', h2⟩ := gcd_local w a b Qa Qb S ha hb
  refine ⟨_, dz hs' sl hsl H A hH ?_, by rw [install_slot sl hsl]; exact h2,
    fun x hx => install_other sl A E' x hx⟩
  intro j
  fin_cases j
  · exact h0
  · exact h1
  all_goals exact hs _ (by decide)

theorem div_step {U : Nat} (sl : Fin 4 → Fin U) (hsl : Function.Injective sl) (n d Qn Qd S : Nat) (hd : 0 < d)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qn (List.replicate n true))
    (h1 : A (sl 1) = ZeroPadding.pad Qd (UnaryTemplate.tape d))
    (h2 : A (sl 2) = List.replicate S false) (h3 : A (sl 3) = List.replicate S false) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl MatrixBucketDivide.machine) (8 * n + 6) H A H A' ∧
      A' (sl 2) = ZeroPadding.pad S (List.replicate (n / d) true) ∧ (∀ x, x ≠ sl 2 → x ≠ sl 3 → A' x = A x) := by
  obtain ⟨E', hs', e0, e1, e2⟩ := div_local n d Qn Qd S hd
  refine ⟨_, dz hs' sl hsl H A hH ?_, by rw [install_slot sl hsl]; exact e2, ?_⟩
  · intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro x hx2 hx3
    by_cases hx : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [install_slot sl hsl]
      fin_cases j
      · exact e0.trans h0.symm
      · exact e1.trans h1.symm
      · exact absurd rfl hx2
      · exact absurd rfl hx3
    · exact install_other sl A E' x (fun j e => hx ⟨j, e⟩)

theorem cmp_step {U : Nat} (a b d l : Fin U) (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ l) (h4 : b ≠ d)
    (h5 : b ≠ l) (h6 : d ≠ l) (x y Qa Qb S C : Nat)
    (hC : min x y + 2 ≤ C) (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ z, z = a ∨ z = b ∨ z = d ∨ z = l → H z = 0)
    (ha : A a = ZeroPadding.pad Qa (UnaryTemplate.tape x))
    (hb : A b = ZeroPadding.pad Qb (List.replicate y true))
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (RecoveryFocus.machine (![a, b, d, l] : Fin 4 → Fin U) MatrixBucketDimensions.Compare.machine)
      (2 * min x y + 6) H A H (Function.update A d (ZeroPadding.pad S [decide (x ≤ y)])) :=
  SLoad.step_update (cmp_local x y Qa Qb S C hC) 2
    (by
      intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd rfl hi
      · rfl)
    _ (SLoad.MaskFrame.quad_injective a b d l h1 h2 h3 h4 h5 h6) H A
    (by
      intro i
      fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH _ (Or.inr (Or.inr (Or.inr rfl))))
    (by
      intro i
      fin_cases i
      · exact ha
      · exact hb
      · exact hd
      · exact hl)

def fixedM {U : Nat} (d l : Fin U) (w : List Bool) :=
  RecoveryFocus.machine (![d, l] : Fin 2 → Fin U) (HierarchyFixedWord.machine w)

theorem fixed_step {U : Nat} (d l : Fin U) (h1 : d ≠ l) (w : List Bool) (S C : Nat)
    (hC : w.length ≤ C) (H : Fin U → Nat) (A : Fin U → List Bool) (hHd : H d = 0) (hHl : H l = 0)
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (fixedM d l w) (2 * w.length + 2) H A H (Function.update A d (ZeroPadding.pad S w)) :=
  SLoad.step_update (fixed_local w S C hC) 0
    (by
      intro i hi
      fin_cases i
      · exact absurd rfl hi
      · rfl)
    _ (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij h1 | exact absurd hij.symm h1) H A
    (by
      intro i
      fin_cases i
      · exact hHd
      · exact hHl)
    (by
      intro i
      fin_cases i
      · exact hd
      · exact hl)

/-- `A'` agrees with `A` outside the index window `[lo, hi]`. -/
def Keep {U : Nat} (lo hi : Nat) (A A' : Fin U → List Bool) : Prop :=
  ∀ x : Fin U, x.val < lo ∨ hi < x.val → A' x = A x

theorem keep_upd {U : Nat} (A : Fin U → List Bool) (d : Fin U) (v : List Bool) :
    Keep d.val d.val A (Function.update A d v) := by
  intro x hx
  rw [Function.update_of_ne]
  intro e
  subst e
  omega

theorem keep_dock {t U : Nat} (sl : Fin t → Fin U) (A A' : Fin U → List Bool)
    (hk : ∀ x, (∀ j, sl j ≠ x) → A' x = A x) (lo hi : Nat)
    (hr : ∀ j, lo ≤ (sl j).val ∧ (sl j).val ≤ hi) : Keep lo hi A A' := by
  intro x hx
  apply hk x
  intro j e
  subst e
  have := hr j
  omega

theorem keep_tobin {U : Nat} (sl : Fin 16 → Fin U) (A A' : Fin U → List Bool)
    (hk : ∀ x, x ≠ sl 2 → (∀ j : Fin 16, 4 ≤ j.val → sl j ≠ x) → A' x = A x) (lo hi : Nat)
    (hr : ∀ j : Fin 16, (j.val = 2 ∨ 4 ≤ j.val) → lo ≤ (sl j).val ∧ (sl j).val ≤ hi) : Keep lo hi A A' := by
  intro x hx
  apply hk x
  · rintro rfl
    have := hr 2 (Or.inl rfl)
    omega
  · intro j hj e
    subst e
    have := hr j (Or.inr hj)
    omega

theorem keep_two {U : Nat} (a b : Fin U) (A A' : Fin U → List Bool) (hk : ∀ x, x ≠ a → x ≠ b → A' x = A x)
    (lo hi : Nat) (ha : lo ≤ a.val ∧ a.val ≤ hi) (hb : lo ≤ b.val ∧ b.val ≤ hi) : Keep lo hi A A' := by
  intro x hx
  apply hk x
  · rintro rfl
    omega
  · rintro rfl
    omega

theorem lt_pow_add (n m : Nat) : n < 2 ^ (n + m) :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))

/-! ## (1) Divide: `1^N, 1^D₀, 1^K ↦ 1^(N/g), 1^(D₀K/g)`, `g = gcd N (D₀K)` -/

def dsl4 : Fin 16 → Fin 48 := ![0, 6, 7, 3, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def dsl5 : Fin 16 → Fin 48 := ![5, 6, 20, 3, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
def dsl6 : Fin 7 → Fin 48 := ![7, 20, 33, 34, 35, 36, 37]
def dsl7 : Fin 7 → Fin 48 := ![33, 38, 39, 40, 41, 42, 43]
def dsl8 : Fin 4 → Fin 48 := ![0, 40, 44, 45]
def dsl9 : Fin 4 → Fin 48 := ![5, 40, 46, 47]

/-- Local universe `Fin 48`: `0` `1^N` · `1` `1^D₀` · `2` `1^K` · `3` log · `4` `word K` · `5` `1^D` · `6` `1^W` ·
`7`/`20` `N`/`D` in framed binary · `33` `g` in framed binary · `40` `word g` · `44` `1^(N/g)` · `46` `1^(D/g)` · rest scratch. -/
def divideM := Composition.machine (Count.wordM false (2 : Fin 48) 4 3)
  (Composition.machine (Count.mulM (1 : Fin 48) 4 5 3)
  (Composition.machine (Count.sumM (0 : Fin 48) 5 6 3)
  (Composition.machine (RecoveryFocus.machine dsl4 tobinM)
  (Composition.machine (RecoveryFocus.machine dsl5 tobinM)
  (Composition.machine (RecoveryFocus.machine dsl6 gcdM)
  (Composition.machine (unaryM dsl7)
  (Composition.machine (RecoveryFocus.machine dsl8 MatrixBucketDivide.machine)
  (RecoveryFocus.machine dsl9 MatrixBucketDivide.machine))))))))

def divideCost (N D4 K : Nat) : Nat :=
  (2 * K + 8) + 1 + ((2 * (D4 * (2 * K + 3) + 2) + 2) + 1 + ((2 * (N + D4 * K) + 6) + 1 +
  (tobinCost N (N + D4 * K) + 1 + (tobinCost (D4 * K) (N + D4 * K) + 1 +
  (gcdCost (N + D4 * K) N (D4 * K) + 1 + (ub (binary (N + D4 * K) (Nat.gcd N (D4 * K))) + 1 +
  ((8 * N + 6) + 1 + (8 * (D4 * K) + 6))))))))

/-- The blank widths the divide stage needs. -/
structure DivideFits (N D4 K S C : Nat) : Prop where
  k1 : K + 2 ≤ S
  k2 : K + 3 ≤ C
  m1 : D4 * (2 * K + 3) + 2 ≤ C
  w1 : 2 * (N + D4 * K) + 2 ≤ C
  g1 : D4 * K + 2 ≤ S

theorem divide_run (N D4 K Qa Qk S C : Nat) (E : Fin 48 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Qa (List.replicate N true)) (h1 : E 1 = ZeroPadding.pad Qa (List.replicate D4 true))
    (h2 : E 2 = ZeroPadding.pad Qk (List.replicate K true)) (h3 : E 3 = List.replicate C false)
    (hscr : ∀ j : Fin 48, 4 ≤ j.val → E j = List.replicate S false)
    (hD : 0 < D4) (hK : 0 < K) (hf : DivideFits N D4 K S C) :
    ∃ E' : Fin 48 → List Bool, Step divideM (divideCost N D4 K) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 44 = ZeroPadding.pad S (List.replicate (N / Nat.gcd N (D4 * K)) true) ∧
      E' 46 = ZeroPadding.pad S (List.replicate (D4 * K / Nat.gcd N (D4 * K)) true) ∧
      (∀ j : Fin 48, j.val < 4 → E' j = E j) := by
  have hDpos : 0 < D4 * K := Nat.mul_pos hD hK
  have hgpos : 0 < Nat.gcd N (D4 * K) := Nat.gcd_pos_of_pos_right N hDpos
  have hgD : Nat.gcd N (D4 * K) ≤ D4 * K := Nat.gcd_le_right N hDpos
  have hNW : N < 2 ^ (N + D4 * K) := lt_pow_add N (D4 * K)
  have hDW : D4 * K < 2 ^ (N + D4 * K) := by
    have := lt_pow_add (D4 * K) N
    rwa [Nat.add_comm (D4 * K) N] at this
  have hgW : Nat.gcd N (D4 * K) < 2 ^ (N + D4 * K) := lt_of_le_of_lt hgD hDW
  -- 1. word K
  have s1 := Count.word0_step (2 : Fin 48) 4 3 (by decide) (by decide) (by decide) K Qk S C hf.k1 hf.k2
    (fun _ => 0) E (fun _ _ => rfl) h2 (hscr 4 (by decide)) h3
  set E1 := Function.update E (4 : Fin 48) (ZeroPadding.pad S (CompareMachine.word K)) with hE1
  have k1 : Keep 4 4 E E1 := keep_upd E 4 _
  -- 2. D = D₀·K
  have s2 := Count.mul_step (1 : Fin 48) 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) D4 K Qa S S C hf.m1 (fun _ => 0) E1 (fun _ _ => rfl) ((k1 1 (by decide)).trans h1)
    (by rw [hE1, Function.update_self]) ((k1 5 (by decide)).trans (hscr 5 (by decide))) ((k1 3 (by decide)).trans h3)
  set E2 := Function.update E1 (5 : Fin 48) (ZeroPadding.pad S (List.replicate (D4 * K) true)) with hE2
  have k2 : Keep 5 5 E1 E2 := keep_upd E1 5 _
  -- 3. W = N + D
  have s3 := Count.sum_step (0 : Fin 48) 5 6 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) N (D4 * K) Qa S S C (by have := hf.w1; omega) (fun _ => 0) E2 (fun _ _ => rfl)
    ((k2 0 (by decide)).trans ((k1 0 (by decide)).trans h0)) (by rw [hE2, Function.update_self])
    ((k2 6 (by decide)).trans ((k1 6 (by decide)).trans (hscr 6 (by decide))))
    ((k2 3 (by decide)).trans ((k1 3 (by decide)).trans h3))
  set E3 := Function.update E2 (6 : Fin 48) (ZeroPadding.pad S (List.replicate (N + D4 * K) true)) with hE3
  have k3 : Keep 6 6 E2 E3 := keep_upd E2 6 _
  have b3 : ∀ x : Fin 48, 6 < x.val → E3 x = List.replicate S false := fun x hx =>
    (k3 x (Or.inr hx)).trans ((k2 x (Or.inr (by omega))).trans ((k1 x (Or.inr (by omega))).trans (hscr x (by omega))))
  have e3N : E3 0 = ZeroPadding.pad Qa (List.replicate N true) :=
    (k3 0 (by decide)).trans ((k2 0 (by decide)).trans ((k1 0 (by decide)).trans h0))
  have e3D : E3 5 = ZeroPadding.pad S (List.replicate (D4 * K) true) := by
    rw [k3 5 (by decide), hE2, Function.update_self]
  have e3W : E3 6 = ZeroPadding.pad S (List.replicate (N + D4 * K) true) := by
    rw [hE3, Function.update_self]
  have e3L : E3 3 = List.replicate C false :=
    (k3 3 (by decide)).trans ((k2 3 (by decide)).trans ((k1 3 (by decide)).trans h3))
  -- 4. N in framed binary at width W
  obtain ⟨E4, s4, o4, t4⟩ := tobin_step dsl4 (by decide) N (N + D4 * K) Qa S S S C (fun _ => 0) E3
    (fun _ => rfl) e3N e3W (b3 7 (by decide)) e3L
    (fun j hj => b3 _ (by revert hj; fin_cases j <;> decide)) (by have := hf.w1; omega) (by have := hf.w1; omega)
  have k4 : Keep 7 19 E3 E4 := keep_tobin dsl4 E3 E4 t4 7 19 (by decide)
  -- 5. D in framed binary at width W
  obtain ⟨E5, s5, o5, t5⟩ := tobin_step dsl5 (by decide) (D4 * K) (N + D4 * K) S S S S C (fun _ => 0) E4
    (fun _ => rfl) ((k4 5 (by decide)).trans e3D) ((k4 6 (by decide)).trans e3W)
    ((k4 20 (by decide)).trans (b3 20 (by decide))) ((k4 3 (by decide)).trans e3L)
    (fun j hj => (k4 _ (by revert hj; fin_cases j <;> decide)).trans (b3 _ (by revert hj; fin_cases j <;> decide)))
    (by have := hf.w1; omega) (by have := hf.w1; omega)
  have k5 : Keep 20 32 E4 E5 := keep_tobin dsl5 E4 E5 t5 20 32 (by decide)
  
  obtain ⟨E6, s6, o6, t6⟩ := gcd_step dsl6 (by decide) (N + D4 * K) N (D4 * K) S S S hNW hDW (fun _ => 0) E5
    (fun _ => rfl) ((k5 7 (by decide)).trans o4) o5
    (fun j hj => (k5 _ (by revert hj; fin_cases j <;> decide)).trans ((k4 _ (by revert hj; fin_cases j <;> decide)).trans
      (b3 _ (by revert hj; fin_cases j <;> decide))))
  have k6 : Keep 7 37 E5 E6 := keep_dock dsl6 E5 E6 t6 7 37 (by decide)
  -- 7. g back to unary / `word g`
  obtain ⟨E7, s7, o7, _, t7⟩ := unary_step dsl7 (by decide) (binary (N + D4 * K) (Nat.gcd N (D4 * K))) S S
    (fun _ => 0) E6 (fun _ => rfl) o6
    (fun j hj => (k6 _ (by revert hj; fin_cases j <;> decide)).trans ((k5 _ (by revert hj; fin_cases j <;> decide)).trans
      ((k4 _ (by revert hj; fin_cases j <;> decide)).trans (b3 _ (by revert hj; fin_cases j <;> decide)))))
  have k7 : Keep 33 43 E6 E7 := keep_dock dsl7 E6 E7 t7 33 43 (by decide)
  have e7g : E7 40 = ZeroPadding.pad S (UnaryTemplate.tape (Nat.gcd N (D4 * K))) := by
    rw [← ExtDecompositionBatch.pad_template S _ (by have := hf.g1; omega)]
    have := o7
    rw [binary_value _ _ hgW, show dsl7 3 = (40 : Fin 48) by decide] at this
    exact this
  have e7N : E7 0 = ZeroPadding.pad Qa (List.replicate N true) :=
    (k7 0 (by decide)).trans ((k6 0 (by decide)).trans ((k5 0 (by decide)).trans ((k4 0 (by decide)).trans e3N)))
  have e7D : E7 5 = ZeroPadding.pad S (List.replicate (D4 * K) true) :=
    (k7 5 (by decide)).trans ((k6 5 (by decide)).trans ((k5 5 (by decide)).trans ((k4 5 (by decide)).trans e3D)))
  have b7 : ∀ x : Fin 48, 43 < x.val → E7 x = List.replicate S false := fun x hx =>
    (k7 x (Or.inr hx)).trans ((k6 x (Or.inr (by omega))).trans ((k5 x (Or.inr (by omega))).trans
      ((k4 x (Or.inr (by omega))).trans (b3 x (by omega)))))
  -- 8. N / g
  obtain ⟨E8, s8, o8, t8⟩ := div_step dsl8 (by decide) N (Nat.gcd N (D4 * K)) Qa S S hgpos (fun _ => 0) E7
    (fun _ => rfl) e7N e7g (b7 44 (by decide)) (b7 45 (by decide))
  have k8 : Keep 44 45 E7 E8 := keep_two 44 45 E7 E8 t8 44 45 (by decide) (by decide)
  -- 9. D / g
  obtain ⟨E9, s9, o9, t9⟩ := div_step dsl9 (by decide) (D4 * K) (Nat.gcd N (D4 * K)) S S S hgpos (fun _ => 0) E8
    (fun _ => rfl) ((k8 5 (by decide)).trans e7D) ((k8 40 (by decide)).trans e7g)
    ((k8 46 (by decide)).trans (b7 46 (by decide))) ((k8 47 (by decide)).trans (b7 47 (by decide)))
  have k9 : Keep 46 47 E8 E9 := keep_two 46 47 E8 E9 t9 46 47 (by decide) (by decide)
  have hall : Step divideM _ (fun _ => 0) E (fun _ => 0) E9 :=
    s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq s9)))))))
  refine ⟨E9, hall, (k9 44 (by decide)).trans o8, o9, ?_⟩
  intro j hj
  have h9 := k9 j (Or.inl (by omega))
  have h8 := k8 j (Or.inl (by omega))
  have h7 := k7 j (Or.inl (by omega))
  have h6 := k6 j (Or.inl (by omega))
  have h5 := k5 j (Or.inl (by omega))
  have h4 := k4 j (Or.inl (by omega))
  have h3' := k3 j (Or.inl (by omega))
  have h2' := k2 j (Or.inl (by omega))
  have h1' := k1 j (Or.inl (by omega))
  rw [h9, h8, h7, h6, h5, h4, h3', h2', h1']

/-! ## (2) Sign split: `1^σ, 1^M ↦ 1^(M or 0)` on the positive / negative port by the parity of `σ` -/

/-- Local universe `Fin 14`: `0` `1^σ` · `1` `1^M` · `2` log · `3` `tape 2` · `4` `1^(σ/2)` · `5` scratch · `6` zero ·
`7` copy of `σ/2` · `8` `1^(2·(σ/2))` · `9` `word σ` · `10` the flag `[σ even]` · `11` zero · `12` positive · `13` negative. -/
def signM := Composition.machine (fixedM (3 : Fin 14) 2 (UnaryTemplate.tape 2))
  (Composition.machine (RecoveryFocus.machine (![0, 3, 4, 5] : Fin 4 → Fin 14) MatrixBucketDivide.machine)
  (Composition.machine (Count.sumM (4 : Fin 14) 6 7 2)
  (Composition.machine (Count.sumM (4 : Fin 14) 7 8 2)
  (Composition.machine (Count.wordM false (0 : Fin 14) 9 2)
  (Composition.machine (RecoveryFocus.machine (![9, 8, 10, 2] : Fin 4 → Fin 14) MatrixBucketDimensions.Compare.machine)
  (CloseoutRowsOriginalSwitch.machine (Count.sumM (1 : Fin 14) 11 12 2) (Count.sumM (1 : Fin 14) 11 13 2)
    (10 : Fin 14)))))))

def signCost (σ M : Nat) : Nat :=
  (2 * (UnaryTemplate.tape 2).length + 2) + 1 + ((8 * σ + 6) + 1 + ((2 * (σ / 2 + 0) + 6) + 1 +
  ((2 * (σ / 2 + (σ / 2 + 0)) + 6) + 1 + ((2 * σ + 8) + 1 + ((2 * min σ (σ / 2 + (σ / 2 + 0)) + 6) + 1 +
  ((2 * (M + 0) + 6) + 2))))))

structure SignFits (σ M S C : Nat) : Prop where
  s1 : σ + 2 ≤ S
  c1 : σ + 4 ≤ C
  c2 : M + 2 ≤ C

theorem even_iff (σ : Nat) : σ ≤ σ / 2 + (σ / 2 + 0) ↔ σ % 2 = 0 := by omega

theorem sign_run (σ M Qa S C : Nat) (E : Fin 14 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Qa (List.replicate σ true)) (h1 : E 1 = ZeroPadding.pad Qa (List.replicate M true))
    (h2 : E 2 = List.replicate C false) (hscr : ∀ j : Fin 14, 3 ≤ j.val → E j = List.replicate S false)
    (hf : SignFits σ M S C) :
    ∃ E' : Fin 14 → List Bool, Step signM (signCost σ M) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 12 = ZeroPadding.pad S (List.replicate (if σ % 2 = 0 then M else 0) true) ∧
      E' 13 = ZeroPadding.pad S (List.replicate (if σ % 2 = 0 then 0 else M) true) ∧
      (∀ j : Fin 14, j.val < 3 → E' j = E j) := by
  have hz : ZeroPadding.pad S (List.replicate 0 true) = List.replicate S false := pad_nil S
  -- 1. the template of 2
  have s1 := fixed_step (3 : Fin 14) 2 (by decide) (UnaryTemplate.tape 2) S C
    (by have := hf.c1; simp [UnaryTemplate.tape]; omega) (fun _ => 0) E rfl rfl (hscr 3 (by decide)) h2
  set E1 := Function.update E (3 : Fin 14) (ZeroPadding.pad S (UnaryTemplate.tape 2)) with hE1
  have k1 : Keep 3 3 E E1 := keep_upd E 3 _
  -- 2. σ / 2
  obtain ⟨E2, s2, o2, t2⟩ := div_step (![0, 3, 4, 5] : Fin 4 → Fin 14) (by decide) σ 2 Qa S S (by decide)
    (fun _ => 0) E1 (fun _ => rfl) ((k1 0 (by decide)).trans h0) (by show E1 3 = _; rw [hE1, Function.update_self])
    ((k1 4 (by decide)).trans (hscr 4 (by decide))) ((k1 5 (by decide)).trans (hscr 5 (by decide)))
  have k2 : Keep 4 5 E1 E2 := keep_two 4 5 E1 E2 t2 4 5 (by decide) (by decide)
  have b2 : ∀ x : Fin 14, 5 < x.val → E2 x = List.replicate S false := fun x hx =>
    (k2 x (Or.inr hx)).trans ((k1 x (Or.inr (by omega))).trans (hscr x (by omega)))
  have e2L : E2 2 = List.replicate C false := (k2 2 (by decide)).trans ((k1 2 (by decide)).trans h2)
  -- 3. copy σ/2, 4. 2·(σ/2)
  have s3 := Count.sum_step (4 : Fin 14) 6 7 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (σ / 2) 0 S S S C (by have := hf.c1; omega) (fun _ => 0) E2 (fun _ _ => rfl) o2
    ((b2 6 (by decide)).trans hz.symm) (b2 7 (by decide)) e2L
  set E3 := Function.update E2 (7 : Fin 14) (ZeroPadding.pad S (List.replicate (σ / 2 + 0) true)) with hE3
  have k3 : Keep 7 7 E2 E3 := keep_upd E2 7 _
  have s4 := Count.sum_step (4 : Fin 14) 7 8 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (σ / 2) (σ / 2 + 0) S S S C (by have := hf.c1; omega) (fun _ => 0) E3 (fun _ _ => rfl)
    ((k3 4 (by decide)).trans o2) (by rw [hE3, Function.update_self]) ((k3 8 (by decide)).trans (b2 8 (by decide)))
    ((k3 2 (by decide)).trans e2L)
  set E4 := Function.update E3 (8 : Fin 14) (ZeroPadding.pad S (List.replicate (σ / 2 + (σ / 2 + 0)) true))
    with hE4
  have k4 : Keep 8 8 E3 E4 := keep_upd E3 8 _
  -- 5. word σ
  have s5 := Count.word0_step (0 : Fin 14) 9 2 (by decide) (by decide) (by decide) σ Qa S C hf.s1
    (by have := hf.c1; omega) (fun _ => 0) E4 (fun _ _ => rfl)
    ((k4 0 (by decide)).trans ((k3 0 (by decide)).trans ((k2 0 (by decide)).trans ((k1 0 (by decide)).trans h0))))
    ((k4 9 (by decide)).trans ((k3 9 (by decide)).trans (b2 9 (by decide))))
    ((k4 2 (by decide)).trans ((k3 2 (by decide)).trans e2L))
  set E5 := Function.update E4 (9 : Fin 14) (ZeroPadding.pad S (CompareMachine.word σ)) with hE5
  have k5 : Keep 9 9 E4 E5 := keep_upd E4 9 _
  -- 6. the parity flag `[σ ≤ 2·(σ/2)]`
  have s6 := cmp_step (9 : Fin 14) 8 10 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    σ (σ / 2 + (σ / 2 + 0)) S S S C (by have := hf.c1; omega) (fun _ => 0) E5 (fun _ _ => rfl)
    (by rw [hE5, Function.update_self]; exact ExtDecompositionBatch.pad_template S σ hf.s1)
    ((k5 8 (by decide)).trans (by rw [hE4, Function.update_self]))
    ((k5 10 (by decide)).trans ((k4 10 (by decide)).trans ((k3 10 (by decide)).trans (b2 10 (by decide)))))
    ((k5 2 (by decide)).trans ((k4 2 (by decide)).trans ((k3 2 (by decide)).trans e2L)))
  set E6 := Function.update E5 (10 : Fin 14) (ZeroPadding.pad S [decide (σ ≤ σ / 2 + (σ / 2 + 0))]) with hE6
  have k6 : Keep 10 10 E5 E6 := keep_upd E5 10 _
  have e6M : E6 1 = ZeroPadding.pad Qa (List.replicate M true) :=
    (k6 1 (by decide)).trans ((k5 1 (by decide)).trans ((k4 1 (by decide)).trans ((k3 1 (by decide)).trans
      ((k2 1 (by decide)).trans ((k1 1 (by decide)).trans h1)))))
  have b6 : ∀ x : Fin 14, 10 < x.val → E6 x = List.replicate S false := fun x hx =>
    (k6 x (Or.inr hx)).trans ((k5 x (Or.inr (by omega))).trans ((k4 x (Or.inr (by omega))).trans
      ((k3 x (Or.inr (by omega))).trans (b2 x (by omega)))))
  have e6L : E6 2 = List.replicate C false :=
    (k6 2 (by decide)).trans ((k5 2 (by decide)).trans ((k4 2 (by decide)).trans ((k3 2 (by decide)).trans e2L)))
  have keep6 : ∀ j : Fin 14, j.val < 3 → E6 j = E j := by
    intro j hj
    rw [k6 j (Or.inl (by omega)), k5 j (Or.inl (by omega)), k4 j (Or.inl (by omega)), k3 j (Or.inl (by omega)),
      k2 j (Or.inl (by omega)), k1 j (Or.inl (by omega))]
  -- 7. switch on the flag
  cases hev : decide (σ ≤ σ / 2 + (σ / 2 + 0)) with
  | true =>
    have heven : σ % 2 = 0 := (even_iff σ).1 (of_decide_eq_true hev)
    have t7 := Count.sum_step (1 : Fin 14) 11 12 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) M 0 Qa S S C (by have := hf.c2; omega) (fun _ => 0) E6 (fun _ _ => rfl) e6M
      ((b6 11 (by decide)).trans hz.symm) (b6 12 (by decide)) e6L
    have sw := CloseoutRowsOriginalSwitch.true_run (Count.sumM (1 : Fin 14) 11 12 2)
      (Count.sumM (1 : Fin 14) 11 13 2) (10 : Fin 14) t7
      (by show readTapeBit (E6 10) 0 = true; rw [hE6, Function.update_self, hev]; exact Count.read_flag S true)
    refine ⟨_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq sw))))), ?_, ?_, ?_⟩
    · rw [Function.update_self, if_pos heven, Nat.add_zero]
    · rw [Function.update_of_ne (by decide), b6 13 (by decide), if_pos heven, hz]
    · intro j hj
      rw [Function.update_of_ne (by intro e; subst e; simp at hj), keep6 j hj]
  | false =>
    have hodd : ¬ σ % 2 = 0 := fun h => by
      have := (even_iff σ).2 h
      exact Bool.false_ne_true (hev.symm.trans (decide_eq_true this))
    have t7 := Count.sum_step (1 : Fin 14) 11 13 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) M 0 Qa S S C (by have := hf.c2; omega) (fun _ => 0) E6 (fun _ _ => rfl) e6M
      ((b6 11 (by decide)).trans hz.symm) (b6 13 (by decide)) e6L
    have sw := CloseoutRowsOriginalSwitch.false_run (Count.sumM (1 : Fin 14) 11 12 2)
      (Count.sumM (1 : Fin 14) 11 13 2) (10 : Fin 14) t7
      (by show readTapeBit (E6 10) 0 = false; rw [hE6, Function.update_self, hev]; exact Count.read_flag S false)
    refine ⟨_, s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq sw))))), ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by decide), b6 12 (by decide), if_neg hodd, hz]
    · rw [Function.update_self, if_neg hodd, Nat.add_zero]
    · intro j hj
      rw [Function.update_of_ne (by intro e; subst e; simp at hj), keep6 j hj]

/-! ## (3) Emit: `1^b, 1^p, 1^n, 1^d ↦ pad R (frame (binary (width b) ·))` -/

def esl5 : Fin 16 → Fin 49 := ![1, 9, 22, 4, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
def esl6 : Fin 16 → Fin 49 := ![2, 9, 35, 4, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
def esl7 : Fin 16 → Fin 49 := ![3, 9, 48, 4, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

/-- Local universe `Fin 49`: `0` `1^b` · `1`/`2`/`3` `1^p`, `1^n`, `1^d` · `4` log · `5` zero · `6` copy of `b` ·
`7` `1^(2b)` · `8` `1^2` · `9` `1^(width b)` · outputs `22`, `35`, `48` (blank `R`) · the three converters' scratch. -/
def emitM := Composition.machine (Count.sumM (0 : Fin 49) 5 6 4)
  (Composition.machine (Count.sumM (0 : Fin 49) 6 7 4)
  (Composition.machine (fixedM (8 : Fin 49) 4 [true, true])
  (Composition.machine (Count.sumM (7 : Fin 49) 8 9 4)
  (Composition.machine (RecoveryFocus.machine esl5 tobinM)
  (Composition.machine (RecoveryFocus.machine esl6 tobinM)
  (RecoveryFocus.machine esl7 tobinM))))))

def emitCost (b p n d : Nat) : Nat :=
  (2 * (b + 0) + 6) + 1 + ((2 * (b + (b + 0)) + 6) + 1 + ((2 * [true, true].length + 2) + 1 +
  ((2 * (b + (b + 0) + 2) + 6) + 1 + (tobinCost p (b + (b + 0) + 2) + 1 + (tobinCost n (b + (b + 0) + 2) + 1 +
  tobinCost d (b + (b + 0) + 2))))))

structure EmitFits (b p n d C : Nat) : Prop where
  c1 : 4 * b + 6 ≤ C
  c2 : p + 2 ≤ C
  c3 : n + 2 ≤ C
  c4 : d + 2 ≤ C

theorem width_eq (b : Nat) : b + (b + 0) + 2 = CompetitorRationalDecision.width b := by
  simp only [CompetitorRationalDecision.width]
  omega

theorem emit_run (b p n d Qb Qa R S C : Nat) (E : Fin 49 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Qb (List.replicate b true)) (h1 : E 1 = ZeroPadding.pad Qa (List.replicate p true))
    (h2 : E 2 = ZeroPadding.pad Qa (List.replicate n true)) (h3 : E 3 = ZeroPadding.pad Qa (List.replicate d true))
    (h4 : E 4 = List.replicate C false)
    (ho : ∀ j : Fin 49, (j.val = 22 ∨ j.val = 35 ∨ j.val = 48) → E j = List.replicate R false)
    (hscr : ∀ j : Fin 49, 5 ≤ j.val → j.val ≠ 22 → j.val ≠ 35 → j.val ≠ 48 → E j = List.replicate S false)
    (hf : EmitFits b p n d C) :
    ∃ E' : Fin 49 → List Bool, Step emitM (emitCost b p n d) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 22 = ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b) p)) ∧
      E' 35 = ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b) n)) ∧
      E' 48 = ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b) d)) ∧
      (∀ j : Fin 49, j.val < 5 → E' j = E j) := by
  have hz : ZeroPadding.pad S (List.replicate 0 true) = List.replicate S false := pad_nil S
  -- 1.–4. `1^(b + b + 2)`
  have s1 := Count.sum_step (0 : Fin 49) 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) b 0 Qb S S C (by have := hf.c1; omega) (fun _ => 0) E (fun _ _ => rfl) h0
    ((hscr 5 (by decide) (by decide) (by decide) (by decide)).trans hz.symm)
    (hscr 6 (by decide) (by decide) (by decide) (by decide)) h4
  set E1 := Function.update E (6 : Fin 49) (ZeroPadding.pad S (List.replicate (b + 0) true)) with hE1
  have k1 : Keep 6 6 E E1 := keep_upd E 6 _
  have s2 := Count.sum_step (0 : Fin 49) 6 7 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) b (b + 0) Qb S S C (by have := hf.c1; omega) (fun _ => 0) E1 (fun _ _ => rfl)
    ((k1 0 (by decide)).trans h0) (by rw [hE1, Function.update_self])
    ((k1 7 (by decide)).trans (hscr 7 (by decide) (by decide) (by decide) (by decide))) ((k1 4 (by decide)).trans h4)
  set E2 := Function.update E1 (7 : Fin 49) (ZeroPadding.pad S (List.replicate (b + (b + 0)) true)) with hE2
  have k2 : Keep 7 7 E1 E2 := keep_upd E1 7 _
  have s3 := fixed_step (8 : Fin 49) 4 (by decide) [true, true] S C (by have := hf.c1; simp; omega) (fun _ => 0) E2
    rfl rfl ((k2 8 (by decide)).trans ((k1 8 (by decide)).trans (hscr 8 (by decide) (by decide) (by decide) (by decide))))
    ((k2 4 (by decide)).trans ((k1 4 (by decide)).trans h4))
  set E3 := Function.update E2 (8 : Fin 49) (ZeroPadding.pad S [true, true]) with hE3
  have k3 : Keep 8 8 E2 E3 := keep_upd E2 8 _
  have s4 := Count.sum_step (7 : Fin 49) 8 9 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (b + (b + 0)) 2 S S S C (by have := hf.c1; omega) (fun _ => 0) E3 (fun _ _ => rfl)
    ((k3 7 (by decide)).trans (by rw [hE2, Function.update_self])) (by rw [hE3, Function.update_self]; rfl)
    ((k3 9 (by decide)).trans ((k2 9 (by decide)).trans ((k1 9 (by decide)).trans
      (hscr 9 (by decide) (by decide) (by decide) (by decide)))))
    ((k3 4 (by decide)).trans ((k2 4 (by decide)).trans ((k1 4 (by decide)).trans h4)))
  set E4 := Function.update E3 (9 : Fin 49) (ZeroPadding.pad S (List.replicate (b + (b + 0) + 2) true)) with hE4
  have k4 : Keep 9 9 E3 E4 := keep_upd E3 9 _
  have b4 : ∀ x : Fin 49, 9 < x.val → x.val ≠ 22 → x.val ≠ 35 → x.val ≠ 48 → E4 x = List.replicate S false :=
    fun x hx a1 a2 a3 => (k4 x (Or.inr hx)).trans ((k3 x (Or.inr (by omega))).trans ((k2 x (Or.inr (by omega))).trans
      ((k1 x (Or.inr (by omega))).trans (hscr x (by omega) a1 a2 a3))))
  have o4 : ∀ x : Fin 49, (x.val = 22 ∨ x.val = 35 ∨ x.val = 48) → E4 x = List.replicate R false :=
    fun x hx => (k4 x (Or.inr (by omega))).trans ((k3 x (Or.inr (by omega))).trans ((k2 x (Or.inr (by omega))).trans
      ((k1 x (Or.inr (by omega))).trans (ho x hx))))
  have in4 : ∀ x : Fin 49, x.val < 5 → E4 x = E x := fun x hx =>
    (k4 x (Or.inl (by omega))).trans ((k3 x (Or.inl (by omega))).trans ((k2 x (Or.inl (by omega))).trans
      (k1 x (Or.inl (by omega)))))
  have w4 : E4 9 = ZeroPadding.pad S (List.replicate (b + (b + 0) + 2) true) := by rw [hE4, Function.update_self]
  -- 5.–7. the three words
  obtain ⟨E5, s5, o5, t5⟩ := tobin_step esl5 (by decide) p (b + (b + 0) + 2) Qa S R S C (fun _ => 0) E4
    (fun _ => rfl) ((in4 1 (by decide)).trans h1) w4 (o4 22 (by decide)) ((in4 4 (by decide)).trans h4)
    (fun j hj => b4 _ (by revert hj; fin_cases j <;> decide) (by revert hj; fin_cases j <;> decide)
      (by revert hj; fin_cases j <;> decide) (by revert hj; fin_cases j <;> decide))
    (by have := hf.c2; omega) (by have := hf.c1; omega)
  have k5 : Keep 10 22 E4 E5 := keep_tobin esl5 E4 E5 t5 10 22 (by decide)
  obtain ⟨E6, s6, o6, t6⟩ := tobin_step esl6 (by decide) n (b + (b + 0) + 2) Qa S R S C (fun _ => 0) E5
    (fun _ => rfl) ((k5 2 (by decide)).trans ((in4 2 (by decide)).trans h2)) ((k5 9 (by decide)).trans w4)
    ((k5 35 (by decide)).trans (o4 35 (by decide))) ((k5 4 (by decide)).trans ((in4 4 (by decide)).trans h4))
    (fun j hj => (k5 _ (by revert hj; fin_cases j <;> decide)).trans (b4 _ (by revert hj; fin_cases j <;> decide)
      (by revert hj; fin_cases j <;> decide) (by revert hj; fin_cases j <;> decide) (by revert hj; fin_cases j <;> decide)))
    (by have := hf.c3; omega) (by have := hf.c1; omega)
  have k6 : Keep 23 35 E5 E6 := keep_tobin esl6 E5 E6 t6 23 35 (by decide)
  obtain ⟨E7, s7, o7, t7⟩ := tobin_step esl7 (by decide) d (b + (b + 0) + 2) Qa S R S C (fun _ => 0) E6
    (fun _ => rfl) ((k6 3 (by decide)).trans ((k5 3 (by decide)).trans ((in4 3 (by decide)).trans h3)))
    ((k6 9 (by decide)).trans ((k5 9 (by decide)).trans w4))
    ((k6 48 (by decide)).trans ((k5 48 (by decide)).trans (o4 48 (by decide))))
    ((k6 4 (by decide)).trans ((k5 4 (by decide)).trans ((in4 4 (by decide)).trans h4)))
    (fun j hj => (k6 _ (by revert hj; fin_cases j <;> decide)).trans ((k5 _ (by revert hj; fin_cases j <;> decide)).trans
      (b4 _ (by revert hj; fin_cases j <;> decide) (by revert hj; fin_cases j <;> decide)
        (by revert hj; fin_cases j <;> decide) (by revert hj; fin_cases j <;> decide))))
    (by have := hf.c4; omega) (by have := hf.c1; omega)
  have k7 : Keep 36 48 E6 E7 := keep_tobin esl7 E6 E7 t7 36 48 (by decide)
  have hall : Step emitM _ (fun _ => 0) E (fun _ => 0) E7 := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))
  rw [width_eq] at o5 o6 o7
  refine ⟨E7, hall, (k7 22 (by decide)).trans ((k6 22 (by decide)).trans o5), (k7 35 (by decide)).trans o6, o7, ?_⟩
  intro j hj
  rw [k7 j (Or.inl (by omega)), k6 j (Or.inl (by omega)), k5 j (Or.inl (by omega)), in4 j hj]

end
end NearCubicWires.SourceFactorSel.CoefReduce

