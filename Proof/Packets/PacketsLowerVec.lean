import Proof.Packets.PacketsMetaWord

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
noncomputable section

theorem sq_cost (x : ℕ) : sqMap.cost x ≤ UnaryCalc.polyCoefficient 2 1 * (x + 3) ^ 3 := by
  change PCPSerializerCapacity.Power.budget 2 1 x ≤ _
  have h := sq_budget_le x
  have hp := Nat.pow_le_pow_left (show x + 1 ≤ x + 3 by omega) 3
  exact h.trans (Nat.mul_le_mul_left _ hp)

/-! ## The kit code bound and the atom capacity -/

/-- The kit code bound: `codeBound + (258·pop + 2)^2`. -/
def kitC (a : DecompositionAlgorithm) (r : Request) : ℕ := codeBound a r + (258 * pop a r + 2) ^ 2

/-- The raw-atom capacity `64·(N + 2)^2`. -/
def capOf (a : DecompositionAlgorithm) (r : Request) : ℕ := 64 * (childTotal a r + 2) ^ 2

theorem codeBound_le_kitC (a : DecompositionAlgorithm) (r : Request) : codeBound a r ≤ kitC a r := by
  unfold kitC; omega

theorem sq_le_kitC (a : DecompositionAlgorithm) (r : Request) : (258 * pop a r + 2) ^ 2 ≤ kitC a r := by
  unfold kitC; omega

/-- **The `kitC` stage.** -/
def kitCStage (a : DecompositionAlgorithm) : UnaryStage a (kitC a) := by
  have h : kitC a = fun r => codeBound a r + 1 * (pop a r * 258 + 1 + 1) ^ 2 :=
    funext (fun r => by unfold kitC; ring)
  rw [h]
  exact (codeBoundStage a).pairP
    ((((popStage a).thenMapP (scaleMap 258) (4 * 258 + 12) 2 (scale_cost 258)).thenMapP (plusMap 1) 6 1
      (plus_cost 1)).thenMapP sqMap (UnaryCalc.polyCoefficient 2 1) 3 sq_cost) addMap2 6 1 add_cost

/-- **The capacity stage.** -/
def capStage (a : DecompositionAlgorithm) : UnaryStage a (capOf a) := by
  have h : capOf a = fun r => 1 * (childTotal a r + 1 + 1) ^ 2 * 64 :=
    funext (fun r => by unfold capOf; ring)
  rw [h]
  exact (((childStage a).thenMapP (plusMap 1) 6 1 (plus_cost 1)).thenMapP sqMap (UnaryCalc.polyCoefficient 2 1) 3
    sq_cost).thenMapP (scaleMap 64) (4 * 64 + 12) 2 (scale_cost 64)

theorem cap_ge (a : DecompositionAlgorithm) (r : Request) :
    64 * (ExtDecompositionBatch.B a (RepairSource.CloseoutRowsUniversal.pool (live a r) (occ a r)) + 2) ^ 2 ≤
      capOf a r := by
  rw [ExtDecompositionBatch.B_eq_sum]
  unfold capOf childTotal childCounts
  exact le_refl _

/-! ## The vector -/

/-- The six words, one fixed machine. -/
def lowerVec (a : DecompositionAlgorithm) (qS : UnaryStage a (fun r => r.q)) (degS : UnaryStage a (degree a))
    (tupS : UnaryStage a (tupleWork a)) (walkS : UnaryStage a (walkLength a)) :=
  ((((((VecStage.nil a (fun _ _ => [])).snoc (kitCStage a).tplP).snoc (kitCStage a).tplP).snoc
    (wStage a qS degS tupS walkS).tplP).snoc (popStage a).tplP).snoc (capStage a).toWord).snoc (countStage a)

structure LowerMetaPG (a : DecompositionAlgorithm) (C w : Request → ℕ) where
  tapes : ℕ
  tapes_ge : 7 ≤ tapes
  states : ℕ
  machine : Machine tapes states
  cost : Request → ℕ
  cM : ℕ
  dM : ℕ
  cost_le : ∀ r, cost r ≤ cM * (r.smallSize a) ^ dM
  cap : Request → ℕ
  cK : ℕ
  dK : ℕ
  cap_le : ∀ r, cap r ≤ cK * (r.smallSize a) ^ dK
  cap_ge : ∀ r, 64 * (ExtDecompositionBatch.B a (RepairSource.CloseoutRowsUniversal.pool (live a r) (occ a r)) + 2) ^ 2
    ≤ cap r
  run : ∀ r, ∃ (H : Fin tapes → ℕ) (A : Fin tapes → List Bool),
    Step machine (cost r) (fun _ => 0)
      (fun i => if i.val = 0 then RepairOrdinary.frame (Request.input a r) else []) H A ∧
    A ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H ⟨0, by omega⟩ = 0 ∧
    A ⟨1, by omega⟩ = UnaryTemplate.tape (C r) ∧ H ⟨1, by omega⟩ = 0 ∧
    A ⟨2, by omega⟩ = UnaryTemplate.tape (C r) ∧ H ⟨2, by omega⟩ = 0 ∧
    A ⟨3, by omega⟩ = UnaryTemplate.tape (w r) ∧ H ⟨3, by omega⟩ = 0 ∧
    A ⟨4, by omega⟩ = UnaryTemplate.tape (r.family a).occurrences.length ∧ H ⟨4, by omega⟩ = 0 ∧
    A ⟨5, by omega⟩ = List.replicate (cap r) true ∧ H ⟨5, by omega⟩ = 0 ∧
    A ⟨6, by omega⟩ = CloseoutRowsRawAtomMeaning.countWord a
      (RepairSource.CloseoutRowsUniversal.pool (live a r) (occ a r)) ∧ H ⟨6, by omega⟩ = 0

/-- **The F2 metadata**, from the typed inputs `q`, `degree`, `tupleWork`, `walkLength`. -/
def lowerMetaPG (a : DecompositionAlgorithm) (qS : UnaryStage a (fun r => r.q)) (degS : UnaryStage a (degree a))
    (tupS : UnaryStage a (tupleWork a)) (walkS : UnaryStage a (walkLength a)) :
    LowerMetaPG a (kitC a) (wOf a) where
  tapes := 1 + 6 + (lowerVec a qS degS tupS walkS).extra
  tapes_ge := by omega
  states := (lowerVec a qS degS tupS walkS).states
  machine := (lowerVec a qS degS tupS walkS).machine
  cost := (lowerVec a qS degS tupS walkS).cost
  cM := (lowerVec a qS degS tupS walkS).coefficient
  dM := (lowerVec a qS degS tupS walkS).degree
  cost_le := (lowerVec a qS degS tupS walkS).cost_le
  cap := capOf a
  cK := (capStage a).coefficient + 7
  dK := (capStage a).degree + 1
  cap_le := fun r => by
    have := (capStage a).value_bound r
    omega
  cap_ge := cap_ge a
  run := by
    intro r
    obtain ⟨H, A, hs, h0, g0, hout⟩ := (lowerVec a qS degS tupS walkS).run r
    exact ⟨H, A, hs, h0, g0, (hout 0 (by omega)).1, (hout 0 (by omega)).2, (hout 1 (by omega)).1,
      (hout 1 (by omega)).2, (hout 2 (by omega)).1, (hout 2 (by omega)).2, (hout 3 (by omega)).1,
      (hout 3 (by omega)).2, (hout 4 (by omega)).1, (hout 4 (by omega)).2, (hout 5 (by omega)).1,
      (hout 5 (by omega)).2⟩

end
end NearCubicWires.PacketsGlue.RequestMeta

