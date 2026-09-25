import Proof.SourceAssembly.SourceFactorSelWordsCostSB

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsCost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-- Every exact gate word is non-empty. -/
theorem exactWord_pos {n : ℕ} (g : ExactThresholdGate n) : 1 ≤ (exactWord g).length := by
  unfold exactWord intWord
  simp only [List.length_append, List.length_cons]
  omega

/-- **The child count is below its word.** -/
theorem gs_le_exact {n : ℕ} (gs : List (ExactThresholdGate n)) : gs.length ≤ (exactListWord gs).length := by
  have h : ∀ l : List (ExactThresholdGate n), l.length ≤ (l.flatMap exactWord).length := by
    intro l
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := exactWord_pos g
      omega
  unfold exactListWord
  rw [List.length_append]
  have := h gs
  omega

/-- **The ten words-stage windows from two numeric facts.** -/
theorem windows_of_Yb (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc : ℕ)
    (hY : 8 * Yb a (r, MB) ≤ Rc) :
    2 * r.nativeWord.length + 1 ≤ Rc ∧ 2 * (r.supportWord a).length + 1 ≤ Rc ∧
    2 * (r.topWord a).length + 1 ≤ Rc ∧ 4 * r.q + 3 ≤ Rc ∧
    4 * normalizedLiveCount r.q r.liveScale + 3 ≤ Rc ∧ 4 * (r.family a).occurrences.length + 3 ≤ Rc ∧
    2 * (r.indexWord a).length + 1 ≤ Rc ∧ 2 * (r.input a).length + 1 ≤ Rc ∧ 2 * MB.length + 1 ≤ Rc := by
  obtain ⟨hq, hn, hs, hi, ht, hN, _, hK⟩ := sizes_le a r
  have hY' : (r.input a).length + MB.length + 1 ≤ Yb a (r, MB) := by
    show _ ≤ (r.input a).length + (exactListWord (gsOf a r)).length + (gsOf a r).length + MB.length + 1
    omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem need_sb_le (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) :
    (NearCubicWires.SourceStart.Bank.sb a).need r ≤ 16777216 * (2 * Yb a (r, MB)) ^ 3 := by
  obtain ⟨hq, hn, _⟩ := sizes_le a r
  have hb : r.nativeWord.length + r.q + 1 ≤ 2 * Yb a (r, MB) := by
    show _ ≤ 2 * ((r.input a).length + (exactListWord (gsOf a r)).length + (gsOf a r).length + MB.length + 1)
    omega
  show PCJ6e421fabe2aa4155_SourcePoolCapacity.value r.nativeWord.length r.q ≤ _
  unfold PCJ6e421fabe2aa4155_SourcePoolCapacity.value
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 3)

end
end NearCubicWires.SourceFactorSel.WordsCost

