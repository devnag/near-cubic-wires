import Proof.Rows.RowsInitLoopAux

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

namespace RowsInit.LoopTable
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta RowsInit.LoopAux
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.RecoveryRootRound
noncomputable section

/-! ## 1. Docking a unary / word map into any bank -/

theorem umap_dock {T : ℕ} {f : ℕ → ℕ} (m : UnaryMap f) (x : ℕ) (sl : Fin (2 + m.extra) → Fin T)
    (hsl : Function.Injective sl) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hH : ∀ i, H (sl i) = 0) (hA : ∀ i, A (sl i) = unIn (2 + m.extra) x i) :
    ∃ H' A', Step (RecoveryFocus.machine sl m.machine) (m.cost x) H A H' A' ∧
      A' (sl ⟨1, by omega⟩) = List.replicate (f x) true ∧ H' (sl ⟨1, by omega⟩) = 0 ∧
      ∀ i, (∀ j, sl j ≠ i) → A' i = A i ∧ H' i = H i := by
  obtain ⟨H1, A1, hs, h1, hh1⟩ := m.run x
  have d := hs.dock sl hsl H A hH hA
  refine ⟨_, _, d, ?_, ?_, fun i hi => ⟨install_other _ _ _ _ hi, dockH_other _ _ _ _ hi⟩⟩
  · rw [install_slot _ hsl]; exact h1
  · rw [dockH_slot _ hsl]; exact hh1

theorem wmap_dock {T : ℕ} {g : ℕ → List Bool} (m : WordMap g) (x : ℕ) (sl : Fin (2 + m.extra) → Fin T)
    (hsl : Function.Injective sl) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hH : ∀ i, H (sl i) = 0) (hA : ∀ i, A (sl i) = unIn (2 + m.extra) x i) :
    ∃ H' A', Step (RecoveryFocus.machine sl m.machine) (m.cost x) H A H' A' ∧
      A' (sl ⟨1, by omega⟩) = g x ∧ H' (sl ⟨1, by omega⟩) = 0 ∧
      ∀ i, (∀ j, sl j ≠ i) → A' i = A i ∧ H' i = H i := by
  obtain ⟨H1, A1, hs, h1, hh1⟩ := m.run x
  have d := hs.dock sl hsl H A hH hA
  refine ⟨_, _, d, ?_, ?_, fun i hi => ⟨install_other _ _ _ _ hi, dockH_other _ _ _ _ hi⟩⟩
  · rw [install_slot _ hsl]; exact h1
  · rw [dockH_slot _ hsl]; exact hh1

theorem sum_dock {T : ℕ} (r s : ℕ) (sl : Fin 4 → Fin T) (hsl : Function.Injective sl)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hH : ∀ i, H (sl i) = 0)
    (h0 : A (sl 0) = List.replicate r true) (h1 : A (sl 1) = List.replicate s true)
    (h2 : A (sl 2) = []) (h3 : A (sl 3) = []) :
    ∃ H' A', Step (RecoveryFocus.machine sl ClockUnarySum.machine) (2*(r+s)+6) H A H' A' ∧
      A' (sl 0) = List.replicate r true ∧ A' (sl 2) = List.replicate (r+s) true ∧ (∀ j, H' (sl j) = 0) ∧
      ∀ i, (∀ j, sl j ≠ i) → A' i = A i ∧ H' i = H i := by
  have d := (UnaryCalc.sum_step r s).dock sl hsl H A hH (by
    intro j; fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3)
  refine ⟨_, _, d, ?_, ?_, ?_, fun i hi => ⟨install_other _ _ _ _ hi, dockH_other _ _ _ _ hi⟩⟩
  · rw [install_slot _ hsl]; rfl
  · rw [install_slot _ hsl]; rfl
  · intro j; rw [dockH_slot _ hsl]

/-! ## 2. The eleven stages on the local layout -/

abbrev N : ℕ := 69

def slA : Fin (2 + 15) → Fin N := ![0, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
def slB : Fin (2 + 1) → Fin N := ![8, 3, 24]
def slC : Fin (2 + 15) → Fin N := ![1, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]
def slD : Fin (2 + 1) → Fin N := ![25, 4, 41]
def slE : Fin (2 + 15) → Fin N := ![2, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]
def slF : Fin 4 → Fin N := ![42, 58, 5, 59]
def slG : Fin 4 → Fin N := ![42, 60, 61, 62]
def slH : Fin 4 → Fin N := ![42, 61, 63, 64]
def slI : Fin (2 + 1) → Fin N := ![63, 65, 66]
def slJ : Fin (2 + 1) → Fin N := ![65, 6, 67]
def slK : Fin (2 + 1) → Fin N := ![42, 7, 68]

theorem injA : Function.Injective slA := by decide
theorem injB : Function.Injective slB := by decide
theorem injC : Function.Injective slC := by decide
theorem injD : Function.Injective slD := by decide
theorem injE : Function.Injective slE := by decide
theorem injF : Function.Injective slF := by decide
theorem injG : Function.Injective slG := by decide
theorem injH : Function.Injective slH := by decide
theorem injI : Function.Injective slI := by decide
theorem injJ : Function.Injective slJ := by decide
theorem injK : Function.Injective slK := by decide

/-- The table machine. -/
def machine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine slA powMap.machine) (RecoveryFocus.machine slB cmpWordMap.machine))
    (RecoveryFocus.machine slC powMap.machine)) (RecoveryFocus.machine slD cmpWordMap.machine))
    (RecoveryFocus.machine slE powMap.machine)) (RecoveryFocus.machine slF ClockUnarySum.machine))
    (RecoveryFocus.machine slG ClockUnarySum.machine)) (RecoveryFocus.machine slH ClockUnarySum.machine))
    (RecoveryFocus.machine slI (plusMap 1).machine)) (RecoveryFocus.machine slJ zerosMap.machine))
    (RecoveryFocus.machine slK zerosMap.machine)

/-- Its cost at `s`. -/
def tableCost (s : ℕ) : ℕ :=
  powMap.cost (s/2) + 1 + cmpWordMap.cost (2^(s/2)) + 1 + powMap.cost ((s+1)/2) + 1 +
    cmpWordMap.cost (2^((s+1)/2)) + 1 + powMap.cost s + 1 + (2*(2^s+0)+6) + 1 + (2*(2^s+0)+6) + 1 +
    (2*(2^s+2^s)+6) + 1 + (plusMap 1).cost (2^s+2^s) + 1 + zerosMap.cost (2^s+2^s+1) + 1 + zerosMap.cost (2^s)

/-- The local input bank: `1^(s/2)`, `1^((s+1)/2)`, `1^s` on tapes 0–2. -/
def tin (s : ℕ) : Fin N → List Bool := fun i =>
  if i.val = 0 then List.replicate (s/2) true else if i.val = 1 then List.replicate ((s+1)/2) true
  else if i.val = 2 then List.replicate s true else []

/-! ## 3. The run -/

/-- Frame bookkeeping: a port no slot of a stage touches keeps content and head. -/
macro "frm" f:ident : tactic => `(tactic| exact ($f _ (by decide)))

theorem table_run (s : ℕ) : ∃ (H' : Fin N → ℕ) (A' : Fin N → List Bool),
    Step machine (tableCost s) (fun _ => 0) (tin s) H' A' ∧
    A' 3 = CompareMachine.word (2^(s/2)) ∧ H' 3 = 0 ∧
    A' 4 = CompareMachine.word (2^((s+1)/2)) ∧ H' 4 = 0 ∧
    A' 5 = List.replicate (2^s) true ∧ H' 5 = 0 ∧
    A' 6 = List.replicate (2*2^s+1) false ∧ H' 6 = 0 ∧
    A' 7 = List.replicate (2^s) false ∧ H' 7 = 0 := by
  -- blank ports of the input
  have tb : ∀ i : Fin N, 3 ≤ i.val → tin s i = [] := by
    intro i hi
    unfold tin
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- A: `1^(2^(s/2))` on 8
  obtain ⟨H1, A1, sA, a1, h1, f1⟩ := umap_dock powMap (s/2) slA injA (fun _ => 0) (tin s) (fun _ => rfl)
    (by intro i; fin_cases i <;> rfl)
  have k1 : ∀ i : Fin N, (∀ j, slA j ≠ i) → 3 ≤ i.val → A1 i = [] ∧ H1 i = 0 := fun i hi h3 =>
    ⟨(f1 i hi).1.trans (tb i h3), (f1 i hi).2⟩
  -- B: counter 1 on 3
  obtain ⟨H2, A2, sB, a2, h2, f2⟩ := wmap_dock cmpWordMap (2^(s/2)) slB injB H1 A1
    (by intro i; fin_cases i
        · exact h1
        · exact (k1 3 (by decide) (by decide)).2
        · exact (k1 24 (by decide) (by decide)).2)
    (by intro i; fin_cases i
        · exact a1
        · exact (k1 3 (by decide) (by decide)).1
        · exact (k1 24 (by decide) (by decide)).1)
  have k2 : ∀ i : Fin N, (∀ j, slA j ≠ i) → (∀ j, slB j ≠ i) → 3 ≤ i.val → A2 i = [] ∧ H2 i = 0 :=
    fun i ha hb h3 => ⟨(f2 i hb).1.trans (k1 i ha h3).1, (f2 i hb).2.trans (k1 i ha h3).2⟩
  -- C: `1^(2^((s+1)/2))` on 25 (input on 1)
  have c1 : A2 1 = List.replicate ((s+1)/2) true ∧ H2 1 = 0 := by
    rw [(f2 1 (by decide)).1, (f2 1 (by decide)).2, (f1 1 (by decide)).1, (f1 1 (by decide)).2]
    exact ⟨rfl, rfl⟩
  obtain ⟨H3, A3, sC, a3, h3, f3⟩ := umap_dock powMap ((s+1)/2) slC injC H2 A2
    (by intro i; fin_cases i
        · exact c1.2
        all_goals exact (k2 _ (by decide) (by decide) (by decide)).2)
    (by intro i; fin_cases i
        · exact c1.1
        all_goals exact (k2 _ (by decide) (by decide) (by decide)).1)
  have k3 : ∀ i : Fin N, (∀ j, slA j ≠ i) → (∀ j, slB j ≠ i) → (∀ j, slC j ≠ i) → 3 ≤ i.val →
      A3 i = [] ∧ H3 i = 0 :=
    fun i ha hb hc h3 => ⟨(f3 i hc).1.trans (k2 i ha hb h3).1, (f3 i hc).2.trans (k2 i ha hb h3).2⟩
  -- D: counter 2 on 4
  obtain ⟨H4, A4, sD, a4, h4, f4⟩ := wmap_dock cmpWordMap (2^((s+1)/2)) slD injD H3 A3
    (by intro i; fin_cases i
        · exact h3
        all_goals exact (k3 _ (by decide) (by decide) (by decide) (by decide)).2)
    (by intro i; fin_cases i
        · exact a3
        all_goals exact (k3 _ (by decide) (by decide) (by decide) (by decide)).1)
  have k4 : ∀ i : Fin N, (∀ j, slA j ≠ i) → (∀ j, slB j ≠ i) → (∀ j, slC j ≠ i) → (∀ j, slD j ≠ i) →
      3 ≤ i.val → A4 i = [] ∧ H4 i = 0 :=
    fun i ha hb hc hd h3 => ⟨(f4 i hd).1.trans (k3 i ha hb hc h3).1, (f4 i hd).2.trans (k3 i ha hb hc h3).2⟩
  -- E: `Q = 1^(2^s)` on 42 (input on 2)
  have c2 : A4 2 = List.replicate s true ∧ H4 2 = 0 := by
    rw [(f4 2 (by decide)).1, (f4 2 (by decide)).2, (f3 2 (by decide)).1, (f3 2 (by decide)).2,
      (f2 2 (by decide)).1, (f2 2 (by decide)).2, (f1 2 (by decide)).1, (f1 2 (by decide)).2]
    exact ⟨rfl, rfl⟩
  obtain ⟨H5, A5, sE, a5, h5, f5⟩ := umap_dock powMap s slE injE H4 A4
    (by intro i; fin_cases i
        · exact c2.2
        all_goals exact (k4 _ (by decide) (by decide) (by decide) (by decide) (by decide)).2)
    (by intro i; fin_cases i
        · exact c2.1
        all_goals exact (k4 _ (by decide) (by decide) (by decide) (by decide) (by decide)).1)
  have k5 : ∀ i : Fin N, 58 ≤ i.val ∨ (5 ≤ i.val ∧ i.val ≤ 7) → A5 i = [] ∧ H5 i = 0 := by
    intro i hi
    have e5 : ∀ j, slE j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    have e4 : ∀ j, slD j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    have e3 : ∀ j, slC j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    have e2 : ∀ j, slB j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    have e1 : ∀ j, slA j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    exact ⟨(f5 i e5).1.trans (k4 i e1 e2 e3 e4 (by omega)).1, (f5 i e5).2.trans (k4 i e1 e2 e3 e4 (by omega)).2⟩
  -- F: copy Q to 5 (C6's `1^(2^s)`)
  obtain ⟨H6, A6, sF, q6, a6, h6, f6⟩ := sum_dock (2^s) 0 slF injF H5 A5
    (by intro i; fin_cases i
        · exact h5
        all_goals exact (k5 _ (by decide)).2)
    a5 (k5 58 (by decide)).1 (k5 5 (by decide)).1 (k5 59 (by decide)).1
  have k6 : ∀ i : Fin N, 60 ≤ i.val ∨ (6 ≤ i.val ∧ i.val ≤ 7) → A6 i = [] ∧ H6 i = 0 := by
    intro i hi
    have e6 : ∀ j, slF j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    exact ⟨(f6 i e6).1.trans (k5 i (by omega)).1, (f6 i e6).2.trans (k5 i (by omega)).2⟩
  -- G: copy Q to 61
  obtain ⟨H7, A7, sG, q7, a7, h7, f7⟩ := sum_dock (2^s) 0 slG injG H6 A6
    (by intro i; fin_cases i
        · exact h6 0
        all_goals exact (k6 _ (by decide)).2)
    q6 (k6 60 (by decide)).1 (k6 61 (by decide)).1 (k6 62 (by decide)).1
  have k7 : ∀ i : Fin N, 63 ≤ i.val ∨ (6 ≤ i.val ∧ i.val ≤ 7) → A7 i = [] ∧ H7 i = 0 := by
    intro i hi
    have e7 : ∀ j, slG j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    exact ⟨(f7 i e7).1.trans (k6 i (by omega)).1, (f7 i e7).2.trans (k6 i (by omega)).2⟩
  -- H: `Q + Q` on 63
  obtain ⟨H8, A8, sH, q8, a8, h8, f8⟩ := sum_dock (2^s) (2^s+0) slH injH H7 A7
    (by intro i; fin_cases i
        · exact h7 0
        · exact h7 2
        all_goals exact (k7 _ (by decide)).2)
    q7 a7 (k7 63 (by decide)).1 (k7 64 (by decide)).1
  have k8 : ∀ i : Fin N, 65 ≤ i.val ∨ (6 ≤ i.val ∧ i.val ≤ 7) → A8 i = [] ∧ H8 i = 0 := by
    intro i hi
    have e8 : ∀ j, slH j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    exact ⟨(f8 i e8).1.trans (k7 i (by omega)).1, (f8 i e8).2.trans (k7 i (by omega)).2⟩
  -- I: `+1` on 65
  obtain ⟨H9, A9, sI, a9, h9, f9⟩ := umap_dock (plusMap 1) (2^s+(2^s+0)) slI injI H8 A8
    (by intro i; fin_cases i
        · exact h8 2
        all_goals exact (k8 _ (by decide)).2)
    (by intro i; fin_cases i
        · exact a8
        all_goals exact (k8 _ (by decide)).1)
  have k9 : ∀ i : Fin N, 67 ≤ i.val ∨ (6 ≤ i.val ∧ i.val ≤ 7) → A9 i = [] ∧ H9 i = 0 := by
    intro i hi
    have e9 : ∀ j, slI j ≠ i := by intro j h; subst h; revert hi; revert j; decide
    exact ⟨(f9 i e9).1.trans (k8 i (by omega)).1, (f9 i e9).2.trans (k8 i (by omega)).2⟩
  -- J: zeros of `2·2^s+1` on 6
  obtain ⟨H10, A10, sJ, a10, h10, f10⟩ := wmap_dock zerosMap (2^s+(2^s+0)+1) slJ injJ H9 A9
    (by intro i; fin_cases i
        · exact h9
        all_goals exact (k9 _ (by decide)).2)
    (by intro i; fin_cases i
        · exact a9
        all_goals exact (k9 _ (by decide)).1)
  -- K: zeros of `2^s` on 7 (driver `Q` on 42, untouched since H)
  have q10 : A10 42 = List.replicate (2^s) true ∧ H10 42 = 0 := by
    rw [(f10 42 (by decide)).1, (f10 42 (by decide)).2, (f9 42 (by decide)).1, (f9 42 (by decide)).2]
    exact ⟨q8, h8 0⟩
  obtain ⟨H11, A11, sK, a11, h11, f11⟩ := wmap_dock zerosMap (2^s) slK injK H10 A10
    (by intro i; fin_cases i
        · exact q10.2
        · change H10 7 = 0
          rw [(f10 7 (by decide)).2]; exact (k9 7 (by decide)).2
        · change H10 68 = 0
          rw [(f10 68 (by decide)).2]; exact (k9 68 (by decide)).2)
    (by intro i; fin_cases i
        · exact q10.1
        · change A10 7 = []
          rw [(f10 7 (by decide)).1]; exact (k9 7 (by decide)).1
        · change A10 68 = []
          rw [(f10 68 (by decide)).1]; exact (k9 68 (by decide)).1)
  have whole := (((((((((sA.seq sB).seq sC).seq sD).seq sE).seq sF).seq sG).seq sH).seq sI).seq sJ).seq sK
  refine ⟨H11, A11, whole.enlarge (by unfold tableCost; simp only [Nat.add_zero]; omega), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [(f11 3 (by decide)).1, (f10 3 (by decide)).1, (f9 3 (by decide)).1, (f8 3 (by decide)).1,
      (f7 3 (by decide)).1, (f6 3 (by decide)).1, (f5 3 (by decide)).1, (f4 3 (by decide)).1, (f3 3 (by decide)).1]
    exact a2
  · rw [(f11 3 (by decide)).2, (f10 3 (by decide)).2, (f9 3 (by decide)).2, (f8 3 (by decide)).2,
      (f7 3 (by decide)).2, (f6 3 (by decide)).2, (f5 3 (by decide)).2, (f4 3 (by decide)).2, (f3 3 (by decide)).2]
    exact h2
  · rw [(f11 4 (by decide)).1, (f10 4 (by decide)).1, (f9 4 (by decide)).1, (f8 4 (by decide)).1,
      (f7 4 (by decide)).1, (f6 4 (by decide)).1, (f5 4 (by decide)).1]
    exact a4
  · rw [(f11 4 (by decide)).2, (f10 4 (by decide)).2, (f9 4 (by decide)).2, (f8 4 (by decide)).2,
      (f7 4 (by decide)).2, (f6 4 (by decide)).2, (f5 4 (by decide)).2]
    exact h4
  · rw [(f11 5 (by decide)).1, (f10 5 (by decide)).1, (f9 5 (by decide)).1, (f8 5 (by decide)).1,
      (f7 5 (by decide)).1]
    rw [show A6 5 = List.replicate (2^s+0) true from a6, Nat.add_zero]
  · rw [(f11 5 (by decide)).2, (f10 5 (by decide)).2, (f9 5 (by decide)).2, (f8 5 (by decide)).2,
      (f7 5 (by decide)).2]
    exact h6 2
  · rw [(f11 6 (by decide)).1, show A10 6 = List.replicate (2^s+(2^s+0)+1) false from a10]
    congr 1
    omega
  · rw [(f11 6 (by decide)).2]
    exact h10
  · exact a11
  · exact h11

/-! ## 4. The cost: linear in `2^s` (table class) -/

theorem pow_cost_le (d : ℕ) : powMap.cost d ≤ 200 * ((2^d + 1) * (d + 1)) := by
  change RepairSource.CloseoutCapacity.Power.budget d ≤ _
  unfold RepairSource.CloseoutCapacity.Power.budget MatrixScorePower.budget MatrixUnaryTemplate.budget
  have h1 : 1 ≤ 2^d := Nat.one_le_two_pow
  nlinarith [Nat.zero_le (2^d * d)]

theorem pow_mono_le {d s : ℕ} (h : d ≤ s) : (2^d + 1) * (d + 1) ≤ (2^s + 1) * (s + 1) := by
  have h2 : 2^d ≤ 2^s := Nat.pow_le_pow_right (by omega) h
  exact Nat.mul_le_mul (by omega) (by omega)

/-- **The table stage costs `O(2^s·s)`**: one `2^residual` factor times a polynomial, charged once per request. -/
theorem table_cost_le (s : ℕ) : tableCost s ≤ 2000 * ((2^s + 1) * (s + 1)) := by
  have p1 := le_trans (pow_cost_le (s/2)) (Nat.mul_le_mul_left 200 (pow_mono_le (show s/2 ≤ s by omega)))
  have p2 := le_trans (pow_cost_le ((s+1)/2))
    (Nat.mul_le_mul_left 200 (pow_mono_le (show (s+1)/2 ≤ s + 1 by omega)))
  have p3 := pow_cost_le s
  have e1 : 2^(s/2) ≤ 2^s := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : 2^((s+1)/2) ≤ 2^(s+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : 2^(s+1) = 2 * 2^s := by ring
  have m1 : (2^(s+1) + 1) * (s + 1 + 1) ≤ 4 * ((2^s + 1) * (s + 1)) := by
    rw [e3]; nlinarith
  unfold tableCost
  change _ + 1 + (2 * (2^(s/2) + 2) + 2) + 1 + _ + 1 + (2 * (2^((s+1)/2) + 2) + 2) + 1 + _ + 1 + _ + 1 + _ + 1 + _ + 1 +
    (2 * (2^s + 2^s + 1 + 1) + 2) + 1 + (2 * (2^s + 2^s + 1) + 4) + 1 + (2 * 2^s + 4) ≤ _
  have h1 : 1 ≤ 2^s := Nat.one_le_two_pow
  have q : 2^s + 1 ≤ (2^s + 1) * (s + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

end
end RowsInit.LoopTable
