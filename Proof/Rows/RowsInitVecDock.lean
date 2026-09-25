import Proof.Rows.RowsInitLoopTable

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.VecDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.RepairOrdinary.RecoveryRootRound PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. Docking a heads-`0` run into a bank with arbitrary heads elsewhere -/

theorem run_dock {t u s n : ℕ} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin t → Fin u) (hi : Function.Injective sl)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (sl j) = 0) (hA : ∀ j, A (sl j) = tin j) :
    Step (RecoveryFocus.machine sl p) n H A H (install sl A tout) :=
  (h.dock sl hi H A hH hA).congr (ExtDecompositionBatch.dockH_existing _ _ _ hH) rfl

/-! ## 2. A `VecStage` under the all-heads masked reset -/

theorem vec_masked {a : DecompositionAlgorithm} {n : ℕ} {outs : ℕ → Request → List Bool}
    (V : VecStage a n outs) (r : Request) :
    ∃ B : Fin (1 + n + V.extra + 1) → List Bool,
      Step (MaskedReset.machine V.machine (fun _ => true)) (2 * V.cost r + 2) (fun _ => 0)
        (Fin.addCases (inBank (1 + n + V.extra) (Request.input a r)) (fun _ : Fin 1 => [])) (fun _ => 0) B ∧
      B ⟨0, by omega⟩ = frame (Request.input a r) ∧
      ∀ j (hj : j < n), B ⟨j + 1, by omega⟩ = outs j r := by
  obtain ⟨H', A', h, a0, -, aj⟩ := V.run r
  obtain ⟨k, -, m⟩ := mask_empty h (fun _ => true) (fun _ _ => rfl)
  refine ⟨Fin.addCases (m := 1 + n + V.extra) (n := 1) (motive := fun _ => List Bool) A'
    (fun _ => List.replicate k false), (m.congr_in (zeros_addCases _ _) rfl).congr (zeros_masked H') rfl, ?_, ?_⟩
  · have e : (⟨0, by omega⟩ : Fin (1 + n + V.extra + 1)) = Fin.castAdd 1 (⟨0, by omega⟩ : Fin (1 + n + V.extra)) :=
      rfl
    rw [e, Fin.addCases_left, a0]
  · intro j hj
    have e : (⟨j + 1, by omega⟩ : Fin (1 + n + V.extra + 1)) =
        Fin.castAdd 1 (⟨j + 1, by omega⟩ : Fin (1 + n + V.extra)) := rfl
    rw [e, Fin.addCases_left, (aj j hj).1]

theorem vin_blank (e : ℕ) (w : List Bool) (j : Fin (e + 1)) (hj : j.val ≠ 0) :
    Fin.addCases (m := e) (n := 1) (motive := fun _ => List Bool) (inBank e w) (fun _ => []) j = [] := by
  revert hj
  refine Fin.addCases (m := e) (n := 1) (fun i => ?_) (fun i => ?_) j
  · intro hj
    rw [Fin.addCases_left]
    have : i.val ≠ 0 := by simpa using hj
    simp [inBank, this]
  · intro _
    rw [Fin.addCases_right]

theorem vin_zero (e : ℕ) (w : List Bool) (h : 0 < e) :
    Fin.addCases (m := e) (n := 1) (motive := fun _ => List Bool) (inBank e w) (fun _ => []) ⟨0, by omega⟩ =
      frame w := by
  have : (⟨0, by omega⟩ : Fin (e + 1)) = Fin.castAdd 1 (⟨0, h⟩ : Fin e) := rfl
  rw [this, Fin.addCases_left]
  simp [inBank]

/-- **A masked `VecStage`, docked.** At an injective slot map whose ports hold the framed request (local `0`) and are
otherwise blank, heads `0`: the ambient head vector is unchanged, the outputs are in place, all else untouched. -/
theorem vec_dock {a : DecompositionAlgorithm} {n : ℕ} {outs : ℕ → Request → List Bool}
    (V : VecStage a n outs) (r : Request) {u : ℕ} (sl : Fin (1 + n + V.extra + 1) → Fin u)
    (hi : Function.Injective sl) (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl ⟨0, by omega⟩) = frame (Request.input a r)) (hA : ∀ j, j.val ≠ 0 → A (sl j) = []) :
    ∃ B : Fin (1 + n + V.extra + 1) → List Bool,
      Step (RecoveryFocus.machine sl (MaskedReset.machine V.machine (fun _ => true))) (2 * V.cost r + 2)
        H A H (install sl A B) ∧
      B ⟨0, by omega⟩ = frame (Request.input a r) ∧ ∀ j (hj : j < n), B ⟨j + 1, by omega⟩ = outs j r := by
  obtain ⟨B, hB, b0, bj⟩ := vec_masked V r
  refine ⟨B, run_dock hB sl hi H A hH (fun j => ?_), b0, bj⟩
  by_cases hj : j.val = 0
  · have e : j = ⟨0, by omega⟩ := Fin.ext hj
    rw [e, h0, vin_zero _ _ (by omega)]
  · rw [hA j hj, vin_blank _ _ j hj]

/-! ## 3. A `VecStage` from an indexed family of word stages -/

/-- Transport a vector stage along a pointwise equality of its (first `n`) outputs. -/
def vecOfEq {a : DecompositionAlgorithm} {n : ℕ} {outs outs' : ℕ → Request → List Bool}
    (V : VecStage a n outs) (h : ∀ j, j < n → ∀ r, outs j r = outs' j r) : VecStage a n outs' where
  extra := V.extra
  states := V.states
  machine := V.machine
  cost := V.cost
  coefficient := V.coefficient
  degree := V.degree
  cost_le := V.cost_le
  run := fun r => by
    obtain ⟨H', A', hs, h0, hh0, hj⟩ := V.run r
    exact ⟨H', A', hs, h0, hh0, fun j hj' => ⟨(hj j hj').1.trans (h j hj' r), (hj j hj').2⟩⟩

/-- The outputs of an indexed family (blank past `n`). -/
def vecOuts {n : ℕ} (w : Fin n → Request → List Bool) (j : ℕ) (r : Request) : List Bool :=
  if h : j < n then w ⟨j, h⟩ r else []

/-- **One fixed machine for an indexed family of words**: the `snoc` chain of the family's word stages. -/
def vecOfFn (a : DecompositionAlgorithm) :
    (n : ℕ) → (w : Fin n → Request → List Bool) → ((j : Fin n) → WordStage a (w j)) → VecStage a n (vecOuts w)
  | 0, _, _ => VecStage.nil a _
  | n + 1, w, s =>
    vecOfEq ((vecOfFn a n (fun j => w j.castSucc) (fun j => s j.castSucc)).snoc (s (Fin.last n))) (by
      intro j hj r
      by_cases hjn : j = n
      · subst hjn
        simp only [vecOuts, dif_pos hj]
        rfl
      · have hj' : j < n := by omega
        simp only [if_neg hjn, vecOuts, dif_pos hj', dif_pos hj]
        rfl)

end
end RowsInit.VecDock
