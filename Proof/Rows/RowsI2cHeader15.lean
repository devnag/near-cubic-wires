import Proof.Rows.RowsI2cCache
import Proof.Rows.RowsI2cMeasure

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.I2c.Header15
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.P1Closure NearCubicWires.PacketFamilyParent
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open RowsConstruction.I2c.VecProg NearCubicWires.BlockPlatform
noncomputable section

/-- The child list of the request's family. -/
abbrev gsOf (a : DecompositionAlgorithm) (r : Request) :=
  NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.childList a (Packets.live (r.family a)) (r.family a).occurrences

/-- **The Header-15 value**: `|exactListWord (childList a live occ)| + 1`. -/
def b15 (a : DecompositionAlgorithm) (r : Request) : ℕ := (exactListWord (gsOf a r)).length + 1

/-! ## 1. The two words -/

def h15W (a : DecompositionAlgorithm) : Fin 2 → Request → List Bool :=
  ![fun r => exactListWord (gsOf a r), fun r => UnaryTemplate.tape r.q]

def h15S (a : DecompositionAlgorithm) : (j : Fin 2) → WordStage a (h15W a j)
  | ⟨0, _⟩ => Cache.cacheStage a
  | ⟨1, _⟩ => (qStage a).tplP

def h15Vec (a : DecompositionAlgorithm) := RowsInit.VecDock.vecOfFn a 2 (h15W a) (h15S a)

/-! ## 2. The program: measure, then `+1` (21 tapes: 0 output, 1 cache, 2 arity template, 3–20 private) -/

def mSlots (j : Fin 17) : Fin (1 + 2 + 18) :=
  ⟨if j.val = 0 then 1 else if j.val = 12 then 2 else 3 + j.val, by have := j.isLt; split_ifs <;> omega⟩
def pSlots (j : Fin (2 + (plusMap 1).extra)) : Fin (1 + 2 + 18) :=
  ⟨if j.val = 0 then 18 else if j.val = 1 then 0 else 20, by split_ifs <;> omega⟩
theorem p_val (j : Fin (2 + (plusMap 1).extra)) : (pSlots j).val = if j.val = 0 then 18 else if j.val = 1 then 0 else 20 :=
  rfl

theorem m_val (j : Fin 17) : (mSlots j).val = if j.val = 0 then 1 else if j.val = 12 then 2 else 3 + j.val := rfl
theorem mSlots_inj : Function.Injective mSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [m_val, m_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem pSlots_inj : Function.Injective pSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [p_val, p_val] at hv
  have hi : i.val < 3 := i.isLt
  have hj : j.val < 3 := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

def measureM := Composition.machine (RecoveryFocus.machine mSlots Measure.machine)
  (RecoveryFocus.machine pSlots (plusMap 1).machine)

theorem coldInput_val {q : ℕ} (gs : List (ExactThresholdGate q)) (j : Fin 17) :
    Measure.coldInput gs j = if j.val = 0 then exactListWord gs else if j.val = 12 then UnaryTemplate.tape q else [] := by
  fin_cases j <;> rfl

def measureCost (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  Measure.budget (gsOf a r) + 1 + (plusMap 1).cost (exactListWord (gsOf a r)).length

theorem measure_run (a : DecompositionAlgorithm) (r : Request) :
    ∃ (H : Fin (1 + 2 + 18) → ℕ) (A : Fin (1 + 2 + 18) → List Bool),
      Step measureM (measureCost a r) (fun _ => 0) (pIn 2 18 (RowsInit.VecDock.vecOuts (h15W a)) r) H A ∧
      A ⟨0, by omega⟩ = List.replicate (b15 a r) true := by
  obtain ⟨T, s1, _, _, _, t15⟩ := Measure.run (gsOf a r)
  have d1 := s1.dock mSlots mSlots_inj (fun _ => 0) (pIn 2 18 (RowsInit.VecDock.vecOuts (h15W a)) r) (fun _ => rfl) (by
    intro j
    rw [coldInput_val]
    by_cases j0 : j.val = 0
    · have e : mSlots j = ⟨0+1, by omega⟩ := Fin.ext (by rw [m_val]; simp [j0])
      rw [e]
      simp only [pIn]
      rw [if_pos (by omega)]
      simp [RowsInit.VecDock.vecOuts, h15W, j0]
    by_cases j12 : j.val = 12
    · have e : mSlots j = ⟨1+1, by omega⟩ := Fin.ext (by rw [m_val]; simp [j12])
      rw [e]
      simp only [pIn]
      rw [if_pos (by omega)]
      simp [RowsInit.VecDock.vecOuts, h15W, j12]
    · simp only [pIn]
      rw [if_neg (by rw [m_val]; simp only [j0, j12, if_false]; omega), if_neg j0, if_neg j12])
  have hz : dockH mSlots (fun _ : Fin (1 + 2 + 18) => 0) (fun _ : Fin 17 => 0) = fun _ => 0 :=
    ExtDecompositionBatch.dockH_existing _ _ _ (fun _ => rfl)
  rw [hz] at d1
  obtain ⟨H2, A2, s2, a21, _⟩ := (plusMap 1).run (exactListWord (gsOf a r)).length
  have off : ∀ i : Fin (1 + 2 + 18), (i.val = 0 ∨ i.val = 20) → ∀ j, mSlots j ≠ i := by
    intro i hi j hj
    have hv := congrArg Fin.val hj
    rw [m_val] at hv
    have := j.isLt
    split_ifs at hv <;> omega
  have d2 := s2.dock pSlots pSlots_inj (fun _ => 0)
    (install mSlots (pIn 2 18 (RowsInit.VecDock.vecOuts (h15W a)) r) T) (fun _ => rfl) (by
      intro j
      have hj : j.val < 3 := j.isLt
      by_cases j0 : j.val = 0
      · have e : pSlots j = mSlots 15 := Fin.ext (by rw [p_val, m_val]; simp [j0])
        rw [e, install_slot _ mSlots_inj, t15]
        simp [unIn, j0]
      · have hoff : (pSlots j).val = 0 ∨ (pSlots j).val = 20 := by rw [p_val]; split_ifs <;> omega
        rw [install_other _ _ _ _ (off _ hoff)]
        simp only [pIn, unIn, j0, if_false]
        rw [if_neg (by rcases hoff with h | h <;> omega)])
  refine ⟨_, _, d1.seq d2, ?_⟩
  have e : (⟨0, by omega⟩ : Fin (1 + 2 + 18)) = pSlots ⟨1, show 1 < 3 by omega⟩ := Fin.ext (by rw [p_val]; simp)
  rw [e, install_slot _ pSlots_inj, a21]
  rfl

/-! ## 3. The cost, and the stage -/

theorem measure_cost_le (a : DecompositionAlgorithm) (r : Request) :
    measureCost a r ≤ (300*((Cache.cacheStage a).coefficient+8)^2) *
      (r.smallSize a)^(2*((Cache.cacheStage a).degree+1)) := by
  have hb := Measure.budget_le (gsOf a r)
  have hw := WordStage.word_bound (Cache.cacheStage a) r
  have hc := (Cache.cacheStage a).cost_le r
  have hin := input_le_small a r
  have hq := PolyBound.q_input_le_smallSize a r
  have hs := one_le_small a r
  set s := r.smallSize a with hsd
  set K := (Cache.cacheStage a).coefficient with hK
  set d := (Cache.cacheStage a).degree with hd
  have p1 : s ≤ s^(d+1) := by
    have := Nat.pow_le_pow_right hs (show 1 ≤ d+1 by omega); rwa [pow_one] at this
  have p2 : s^d ≤ s^(d+1) := Nat.pow_le_pow_right hs (by omega)
  have p0 : 1 ≤ s^(d+1) := Nat.one_le_pow _ _ hs
  have hK2 : K * s^d ≤ K * s^(d+1) := Nat.mul_le_mul_left _ p2
  -- the cache length and the arity are below `(K+8)·s^(d+1)`
  have hX : (exactListWord (gsOf a r)).length + r.q + 1 ≤ (K+8) * s^(d+1) := by
    have e : (K+8) * s^(d+1) = K * s^(d+1) + 8 * s^(d+1) := by ring
    change (exactListWord (gsOf a r)).length ≤ _ at hw
    omega
  have hX2 : ((exactListWord (gsOf a r)).length + r.q + 1)^2 ≤ (K+8)^2 * s^(2*(d+1)) := by
    have := Nat.pow_le_pow_left hX 2
    rw [mul_pow, ← pow_mul, Nat.mul_comm (d+1) 2] at this
    exact this
  have pp : s^(d+1) ≤ s^(2*(d+1)) := Nat.pow_le_pow_right hs (by omega)
  have hK8 : (K+8) * s^(d+1) ≤ (K+8)^2 * s^(2*(d+1)) := by
    have h1 : K+8 ≤ (K+8)^2 := by nlinarith
    exact Nat.mul_le_mul h1 pp
  have p00 : 1 ≤ s^(2*(d+1)) := Nat.one_le_pow _ _ hs
  have hK1 : 1 ≤ (K+8)^2 := Nat.one_le_pow _ _ (by omega)
  have hm1 : 1 ≤ (K+8)^2 * s^(2*(d+1)) := Nat.mul_le_mul hK1 p00
  unfold measureCost
  change Measure.budget (gsOf a r) + 1 + (2 * ((exactListWord (gsOf a r)).length + 1 + 1) + 2) ≤ _
  have e : 300*(K+8)^2 * s^(2*(d+1)) = 256*((K+8)^2 * s^(2*(d+1))) + 44*((K+8)^2 * s^(2*(d+1))) := by ring
  rw [e]
  omega

/-- **The measure program** as a `Prog` on the two words. -/
def measureProg (a : DecompositionAlgorithm) :
    Prog a 2 (RowsInit.VecDock.vecOuts (h15W a)) (fun r => List.replicate (b15 a r) true) where
  extra := 18
  states := _
  machine := measureM
  cost := measureCost a
  coefficient := 300*((Cache.cacheStage a).coefficient+8)^2
  degree := 2*((Cache.cacheStage a).degree+1)
  cost_le := measure_cost_le a
  run := measure_run a

def header15Stage (a : DecompositionAlgorithm) : UnaryStage a (b15 a) :=
  WordStage.toUnary (VecStage.thenProg (h15Vec a) (measureProg a))

end
end RowsConstruction.I2c.Header15
