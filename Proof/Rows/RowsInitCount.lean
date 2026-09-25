import Proof.Packets.PacketsPrimeService

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.Count
open NearCubicWires NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.SupplierPrime NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. The value functions of the two selection-count inputs -/

/-- THR selection count (PM's `|Sel|`): `∏ |children_i|`; `0` off THR. -/
def thrSelOf (a : DecompositionAlgorithm) : Request → ℕ
  | .thr r _ _ _ => ∏ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length
  | _ => 0

/-- SYM offset-tuple count: `∏ (bottomCount+1)`; `0` off SYM. -/
def symSelOf : Request → ℕ
  | .sym r _ _ _ => ∏ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount+1)
  | _ => 0

/-- PM's `|Sel|` IS `thrSelOf` on THR: `card (ThresholdRows.Selection a r)`. -/
theorem thrSelOf_card (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    thrSelOf a (.thr r four L target) = Fintype.card (ThresholdRows.Selection a r) := by
  simp only [thrSelOf, ThresholdRows.Selection, Fintype.card_pi, Fintype.card_fin]

theorem thrSelOf_list (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    thrSelOf a (.thr r four L target) = (Packets.thrSelectionList a r).length := by
  simp only [thrSelOf, Packets.thrSelectionList, RCFive.RowKeys.finiteProduct_length]

theorem symSelOf_list (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) : symSelOf (.sym r four L target) = (Packets.symOffsetList r).length := by
  simp only [symSelOf, Packets.symOffsetList, List.length_map, RCFive.RowKeys.finiteProduct_length]

/-- The stage's value, before it is identified with the row count. -/
def rowsValue (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  (thrSelOf a r + symSelOf r) * seedCount a r * max 1 (primeSumOf (cutoffOf a r))

theorem primeSum_zero : primeSumOf 0 = 0 := by
  unfold primeSumOf
  rw [Finset.sum_eq_zero]
  intro p hp
  have := (mem_primesUpTo.mp hp).2
  omega

theorem primeSum_ge (c : ℕ) (hc : 2 ≤ c) : 2 ≤ primeSumOf c := by
  unfold primeSumOf
  exact Finset.single_le_sum (f := fun p => p) (fun _ _ => Nat.zero_le _)
    (mem_primesUpTo.mpr ⟨Nat.prime_two, hc⟩)

/-- **The value is the family's row count, for every request.** -/
theorem rows_eq (a : DecompositionAlgorithm) (r : Request) : rowsValue a r = (r.family a).rows.length := by
  cases r with
  | terminal => simp [rowsValue, thrSelOf, symSelOf, Request.family]
  | sym r four L target =>
    have hrows : ((Request.sym r four L target).family a).rows.length =
        (RCFive.RowKeys.symKeys r L target).length := by
      change (Packets.symFamily r L target).rows.length = _
      rw [← RCFive.RowKeys.sym_rows_eq r L target, List.length_map]
    rw [hrows, RCFive.RowKeys.sym_count]
    change (0 + ∏ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount+1)) *
      seedCount a (.sym r four L target) * max 1 (primeSumOf 0) = _
    rw [primeSum_zero, Nat.zero_add, show max 1 0 = 1 from rfl, Nat.mul_one, Nat.mul_comm]
    rfl
  | thr r four L target =>
    have hrows : ((Request.thr r four L target).family a).rows.length =
        (RCFive.RowKeys.thrKeys a r L target).length := by
      change (Packets.thrFamily a r L target).rows.length = _
      rw [← RCFive.RowKeys.thr_rows_eq a r L target, List.length_map]
    have h563 : 563 ≤ CloseoutFinalC10ThresholdRows.primeCutoff a r target := by
      unfold CloseoutFinalC10ThresholdRows.primeCutoff
      exact canonicalPrimeCutoff_ge_563 _ _
    have hps := primeSum_ge (CloseoutFinalC10ThresholdRows.primeCutoff a r target) (by omega)
    rw [hrows, RCFive.RowKeys.thr_count, thr_prime_sum, ← thrSelOf_list a r four L target]
    change (thrSelOf a (.thr r four L target) + 0) * seedCount a (.thr r four L target) *
      max 1 (primeSumOf (CloseoutFinalC10ThresholdRows.primeCutoff a r target)) = _
    rw [max_eq_right (by omega), Nat.add_zero, Nat.mul_assoc]
    rfl

/-! ## 2. The stage -/

theorem max1_cost (x : ℕ) : max1Map.cost x ≤ 4 * (x + 3) ^ 1 := by
  change 2 * (x + 1) + 2 ≤ 4 * (x + 3) ^ 1
  rw [pow_one]
  omega

/-- The composed stage at the value `rowsValue` (PG's `pairP`/`thenMapP`). -/
def rawStage (a : DecompositionAlgorithm) (cs : UnaryStage a (cutoffOf a)) (seeds : UnaryStage a (seedCount a))
    (thrSel : UnaryStage a (thrSelOf a)) (symSel : UnaryStage a symSelOf) : UnaryStage a (rowsValue a) :=
  ((thrSel.pairP symSel addMap2 6 1 add_cost).pairP seeds mulMap2 8 2 mul_cost).pairP
    ((primeSumStage a cs).thenMapP max1Map 4 1 max1_cost) mulMap2 8 2 mul_cost

/-- **`rowsCountStage`**: ONE fixed machine (for fixed input stages), from the framed request to
`1^(r.family a).rows.length` on tape 1, heads 0, cost `≤ coefficient · smallSize^degree`. -/
def rowsCountStage (a : DecompositionAlgorithm) (cs : UnaryStage a (cutoffOf a))
    (seeds : UnaryStage a (seedCount a)) (thrSel : UnaryStage a (thrSelOf a)) (symSel : UnaryStage a symSelOf) :
    UnaryStage a (fun r => (r.family a).rows.length) where
  extra := (rawStage a cs seeds thrSel symSel).extra
  states := (rawStage a cs seeds thrSel symSel).states
  machine := (rawStage a cs seeds thrSel symSel).machine
  cost := (rawStage a cs seeds thrSel symSel).cost
  coefficient := (rawStage a cs seeds thrSel symSel).coefficient
  degree := (rawStage a cs seeds thrSel symSel).degree
  cost_le := (rawStage a cs seeds thrSel symSel).cost_le
  run := fun r => by
    obtain ⟨H', A', hs, h0, hh0, h1, hh1⟩ := (rawStage a cs seeds thrSel symSel).run r
    exact ⟨H', A', hs, h0, hh0, by rw [h1, rows_eq], hh1⟩

end
end RowsInit.Count
