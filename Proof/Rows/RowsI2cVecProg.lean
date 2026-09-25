import Proof.Packets.PacketsMetaVec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.I2c.VecProg
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketFamilyParent
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryExecution
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. The program shape -/

/-- The program's entry: tape 0 blank (the output), tapes `1..n` the vector's words, the rest blank. -/
def pIn (n e : ℕ) (outs : ℕ → Request → List Bool) (r : Request) : Fin (1 + n + e) → List Bool :=
  fun i => if 1 ≤ i.val ∧ i.val ≤ n then outs (i.val - 1) r else []

/-- **One fixed program on the vector's words**, its result on tape 0. -/
structure Prog (a : DecompositionAlgorithm) (n : ℕ) (outs : ℕ → Request → List Bool) (w : Request → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (1 + n + extra) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a) ^ degree
  run : ∀ r, ∃ (H : Fin (1 + n + extra) → ℕ) (A : Fin (1 + n + extra) → List Bool),
    Step machine (cost r) (fun _ => 0) (pIn n extra outs r) H A ∧ A ⟨0, by omega⟩ = w r

/-! ## 2. The composite layout: 0 the framed input, 1 the output, `2..n+1` the words, then the vector's and the program's
private tapes -/

def vSlot (n eV eP : ℕ) (j : Fin (1 + n + eV)) : Fin (2 + (n + eV + eP)) :=
  ⟨if j.val = 0 then 0 else j.val + 1, by have := j.isLt; split_ifs <;> omega⟩
def pSlot (n eV eP : ℕ) (j : Fin (1 + n + eP)) : Fin (2 + (n + eV + eP)) :=
  ⟨if j.val = 0 then 1 else if j.val ≤ n then j.val + 1 else j.val + 1 + eV, by have := j.isLt; split_ifs <;> omega⟩

theorem vSlot_val (n eV eP : ℕ) (j : Fin (1 + n + eV)) : (vSlot n eV eP j).val = if j.val = 0 then 0 else j.val + 1 := rfl
theorem pSlot_val (n eV eP : ℕ) (j : Fin (1 + n + eP)) :
    (pSlot n eV eP j).val = if j.val = 0 then 1 else if j.val ≤ n then j.val + 1 else j.val + 1 + eV := rfl

theorem vSlot_inj (n eV eP : ℕ) : Function.Injective (vSlot n eV eP) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [vSlot_val, vSlot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem pSlot_inj (n eV eP : ℕ) : Function.Injective (pSlot n eV eP) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [pSlot_val, pSlot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

variable {a : DecompositionAlgorithm} {n : ℕ} {outs : ℕ → Request → List Bool} {w : Request → List Bool}

/-- The vector, then the program. -/
def core (V : VecStage a n outs) (P : Prog a n outs w) :=
  Composition.machine (RecoveryFocus.machine (vSlot n V.extra P.extra) V.machine)
    (RecoveryFocus.machine (pSlot n V.extra P.extra) P.machine)

theorem core_run (V : VecStage a n outs) (P : Prog a n outs w) (r : Request) :
    ∃ (H' : Fin (2 + (n + V.extra + P.extra)) → ℕ) (A' : Fin (2 + (n + V.extra + P.extra)) → List Bool),
      Step (core V P) (V.cost r + 1 + P.cost r) (fun _ => 0) (inBank (2 + (n + V.extra + P.extra)) (Request.input a r))
        H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ A' ⟨1, by omega⟩ = w r := by
  obtain ⟨H1, A1, s1, a0, _, aj⟩ := V.run r
  have d1 := s1.dock (vSlot n V.extra P.extra) (vSlot_inj _ _ _) (fun _ => 0)
    (inBank (2 + (n + V.extra + P.extra)) (Request.input a r)) (fun _ => rfl)
    (by
      intro j
      simp only [inBank, vSlot_val]
      by_cases hj : j.val = 0 <;> simp [hj])
  obtain ⟨H2, A2, s2, w2⟩ := P.run r
  have offv : ∀ j : Fin (1 + n + P.extra), (j.val = 0 ∨ n < j.val) → ∀ i, vSlot n V.extra P.extra i ≠ pSlot n V.extra P.extra j := by
    intro j hj i hi
    have hv := congrArg Fin.val hi
    rw [vSlot_val, pSlot_val] at hv
    have := i.isLt
    split_ifs at hv <;> omega
  have d2 := s2.dock (pSlot n V.extra P.extra) (pSlot_inj _ _ _)
    (dockH (vSlot n V.extra P.extra) (fun _ => 0) H1)
    (install (vSlot n V.extra P.extra) (inBank (2 + (n + V.extra + P.extra)) (Request.input a r)) A1)
    (by
      intro j
      by_cases hj : j.val = 0 ∨ n < j.val
      · rw [dockH_other _ _ _ _ (offv j hj)]
      · have hj0 : j.val ≠ 0 := fun h => hj (Or.inl h)
        have hjn : j.val ≤ n := by
          by_contra h
          exact hj (Or.inr (by omega))
        have e : pSlot n V.extra P.extra j = vSlot n V.extra P.extra ⟨j.val, by omega⟩ :=
          Fin.ext (by rw [pSlot_val, vSlot_val]; dsimp only; split_ifs <;> omega)
        rw [e, dockH_slot _ (vSlot_inj _ _ _)]
        have := (aj (j.val - 1) (by omega)).2
        have e2 : (⟨j.val - 1 + 1, by omega⟩ : Fin (1 + n + V.extra)) = ⟨j.val, by omega⟩ := Fin.ext (by simp; omega)
        rw [e2] at this
        exact this)
    (by
      intro j
      by_cases hj : j.val = 0 ∨ n < j.val
      · rw [install_other _ _ _ _ (offv j hj)]
        have h1 : ¬ (1 ≤ j.val ∧ j.val ≤ n) := by omega
        have h2 : (pSlot n V.extra P.extra j).val ≠ 0 := by rw [pSlot_val]; split_ifs <;> omega
        simp only [inBank, pIn, h2, h1, if_false]
      · have hj0 : j.val ≠ 0 := fun h => hj (Or.inl h)
        have hjn : j.val ≤ n := by
          by_contra h
          exact hj (Or.inr (by omega))
        have e : pSlot n V.extra P.extra j = vSlot n V.extra P.extra ⟨j.val, by omega⟩ :=
          Fin.ext (by rw [pSlot_val, vSlot_val]; dsimp only; split_ifs <;> omega)
        rw [e, install_slot _ (vSlot_inj _ _ _)]
        have := (aj (j.val - 1) (by omega)).1
        have e2 : (⟨j.val - 1 + 1, by omega⟩ : Fin (1 + n + V.extra)) = ⟨j.val, by omega⟩ := Fin.ext (by simp; omega)
        rw [e2] at this
        rw [this]
        simp only [pIn]
        rw [if_pos (by omega)])
  refine ⟨_, _, d1.seq d2, ?_, ?_⟩
  · have hn : ∀ j, pSlot n V.extra P.extra j ≠ ⟨0, by omega⟩ := by
      intro j hj
      have hv : (pSlot n V.extra P.extra j).val = 0 := congrArg Fin.val hj
      rw [pSlot_val] at hv
      split_ifs at hv
      omega
    rw [install_other _ _ _ _ hn]
    have e : (⟨0, by omega⟩ : Fin (2 + (n + V.extra + P.extra))) = vSlot n V.extra P.extra ⟨0, by omega⟩ :=
      Fin.ext (by rw [vSlot_val]; simp)
    rw [e, install_slot _ (vSlot_inj _ _ _), a0]
  · have e : (⟨1, by omega⟩ : Fin (2 + (n + V.extra + P.extra))) = pSlot n V.extra P.extra ⟨0, by omega⟩ :=
      Fin.ext (by rw [pSlot_val]; simp)
    rw [e, install_slot _ (pSlot_inj _ _ _), w2]

theorem inBank_succ (T : ℕ) (hT : 1 ≤ T) (wd : List Bool) :
    Fin.addCases (inBank T wd) (fun _ : Fin 1 => ([] : List Bool)) = inBank (T + 1) wd := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
  · rw [Fin.addCases_left]; simp [inBank]
  · rw [Fin.addCases_right]; simp [inBank]; omega

theorem heads_succ (T : ℕ) : Fin.addCases (fun _ : Fin T => (0 : ℕ)) (fun _ : Fin 1 => (0 : ℕ)) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
  · rw [Fin.addCases_left]
  · rw [Fin.addCases_right]

/-- **The vector, then the program, as one word stage** (all heads reset). -/
def VecStage.thenProg (V : VecStage a n outs) (P : Prog a n outs w) : WordStage a w where
  extra := n + V.extra + P.extra + 1
  states := _
  machine := MaskedReset.machine (core V P) (fun _ => true)
  cost := fun r => 2 * (V.cost r + 1 + P.cost r) + 2
  coefficient := 2 * (V.coefficient + 1 + P.coefficient) + 2
  degree := V.degree + P.degree
  cost_le := by
    intro r
    have h1 := V.cost_le r
    have h2 := P.cost_le r
    have hs := one_le_small a r
    have p1 : (r.smallSize a) ^ V.degree ≤ (r.smallSize a) ^ (V.degree + P.degree) :=
      Nat.pow_le_pow_right hs (by omega)
    have p2 : (r.smallSize a) ^ P.degree ≤ (r.smallSize a) ^ (V.degree + P.degree) :=
      Nat.pow_le_pow_right hs (by omega)
    have p0 : 1 ≤ (r.smallSize a) ^ (V.degree + P.degree) := Nat.one_le_pow _ _ hs
    have q1 := Nat.mul_le_mul_left V.coefficient p1
    have q2 := Nat.mul_le_mul_left P.coefficient p2
    have e : (2 * (V.coefficient + 1 + P.coefficient) + 2) * (r.smallSize a) ^ (V.degree + P.degree) =
        2 * (V.coefficient * (r.smallSize a) ^ (V.degree + P.degree)) +
          2 * (r.smallSize a) ^ (V.degree + P.degree) +
          2 * (P.coefficient * (r.smallSize a) ^ (V.degree + P.degree)) +
          2 * (r.smallSize a) ^ (V.degree + P.degree) := by ring
    rw [e]
    omega
  run := by
    intro r
    obtain ⟨H', A', s, a0, a1⟩ := core_run V P r
    obtain ⟨k, m⟩ := step_mask0 s (fun _ => true) (fun _ _ => rfl)
    refine ⟨_, _, (m.congr_in (heads_succ _) (inBank_succ _ (by omega) _)), ?_, ?_, ?_, ?_⟩
    · have e : (⟨0, by omega⟩ : Fin (2 + (n + V.extra + P.extra + 1))) =
          Fin.castAdd 1 (⟨0, by omega⟩ : Fin (2 + (n + V.extra + P.extra))) := rfl
      rw [e, Fin.addCases_left, a0]
    · have e : (⟨0, by omega⟩ : Fin (2 + (n + V.extra + P.extra + 1))) =
          Fin.castAdd 1 (⟨0, by omega⟩ : Fin (2 + (n + V.extra + P.extra))) := rfl
      rw [e, Fin.addCases_left]
      rfl
    · have e : (⟨1, by omega⟩ : Fin (2 + (n + V.extra + P.extra + 1))) =
          Fin.castAdd 1 (⟨1, by omega⟩ : Fin (2 + (n + V.extra + P.extra))) := rfl
      rw [e, Fin.addCases_left, a1]
    · have e : (⟨1, by omega⟩ : Fin (2 + (n + V.extra + P.extra + 1))) =
          Fin.castAdd 1 (⟨1, by omega⟩ : Fin (2 + (n + V.extra + P.extra))) := rfl
      rw [e, Fin.addCases_left]
      rfl

/-! ## 3. Length bound of a stage's word; unary word stages are unary stages -/

theorem WordStage.word_bound (s : WordStage a w) (r : Request) :
    (w r).length ≤ 2 * (r.input a).length + 1 + s.cost r + 1 := by
  obtain ⟨H', A', ⟨rc, hr, _, ht, hs⟩, _, _, a1, _⟩ := s.run r
  have hsup := RecoveryTapeSupport.run_support s.machine (s.cost r) _ rc hr
    (RepairOrdinary.frame (Request.input a r)).length 0 (fun _ => le_rfl) (by
      intro i
      change (inBank (2 + s.extra) (Request.input a r) i).length ≤ _
      simp only [inBank]
      split_ifs <;> simp)
  have h1 := hsup ⟨1, by omega⟩
  rw [ht, a1, RepairOrdinary.frame_length] at h1
  have hm : max (2 * (r.input a).length + 1) (0 + rc.steps + 1) ≤ 2 * (r.input a).length + 1 + s.cost r + 1 := by
    omega
  exact h1.trans hm

/-- A word stage with a unary word is a unary stage. -/
def WordStage.toUnary {v : Request → ℕ} (s : WordStage a (fun r => List.replicate (v r) true)) : UnaryStage a v where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  coefficient := s.coefficient
  degree := s.degree
  cost_le := s.cost_le
  run := s.run

end
end RowsConstruction.I2c.VecProg
