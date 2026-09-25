import Proof.Rows.RowsHeaderWRun

/-! # Rows Header writer, part 3: the cost bound and the `HdrSpec` term

**Consumer.** RX's global initializer docks a term of `RowsInit.Hdr.HdrSpec selector a printer`
(`rows-rowlevel-20260923/RowsInitHdrSpec.lean`). `hdrSpecOf h15 P` is that term, for RW's Header-15 stage `h15` and the
Header-282 stage `P` (both typed here, instantiated in `RowsHeaderWFinal`).

**Budget.** `cost := coefficient·(smallSize^degree + headerFuel + C + copyCap + |meta| + 1)` literally (`cost_le` is `le_refl`);
`run` enlarges `RowsHeaderW.run`'s exact stage sum `costOf` to it (`costOf_le`) using ONLY `RowCaps.Good`'s Header clause
(`Header.budget … row ≤ headerFuel` for one row, which exists since the family is nonempty) and each stage's own class:
unwrap `2|meta|+2`; live words `≤ c_L·smallSize^d_L` (`RowsInit.liveCost_le`); pool words `≤ 300·(Header.budget+1)`
(`RowsInit.hdrCost_header`); Header 15 `2·c_15·smallSize^d_15+2`; Header 282 `c_P·(smallSize^d_P+|meta|+1)`; reserves `4·hF+4`.
Nothing is multiplied into a table factor; no numeric premise besides `Good` and `rows ≠ []` (both supplied by the consumer).
-/

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsHeaderW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.PacketsGlue.RequestMeta
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. The live-word constants (chosen from `a` alone) -/

def liveC (a : DecompositionAlgorithm) : ℕ := Classical.choose (RowsInit.liveCost_le a)
def liveD (a : DecompositionAlgorithm) : ℕ := Classical.choose (Classical.choose_spec (RowsInit.liveCost_le a))

theorem liveCost_bound (a : DecompositionAlgorithm) (r : Request) :
    RowsInit.liveCost a r ≤ liveC a * (r.smallSize a) ^ liveD a :=
  Classical.choose_spec (Classical.choose_spec (RowsInit.liveCost_le a)) r

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)

/-! ## 2. The bound -/

def coefOf (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) : ℕ :=
  400 + liveC a + 2 * h15.coefficient + P.coefficient
def degOf (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) : ℕ :=
  max (liveD a) (max h15.degree (max P.degree 1))

/-- `HdrSpec.cost`, literally the consumer's bound. -/
def boundOf (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) : ℕ :=
  coefOf selector a h15 P * ((r.smallSize a) ^ degOf selector a h15 P + caps.headerFuel + layout.C + caps.copyCap +
    (rowMetadataWord layout.w layout.degree layout.C caps).length + 1)

/-- **The stage sum fits the bound** for `Good` caps of a nonempty family. -/
theorem costOf_le (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (hG : RowCaps.Good selector a printer r layout facts caps) (hne : (r.family a).rows ≠ []) :
    costOf selector a h15 P r layout caps ≤ boundOf selector a h15 P r layout caps := by
  have hmem := List.head_mem hne
  have hA := RowsInit.hdrCost_header a (r.family a) (geometryOf selector a r) layout ((r.family a).rows.head hne)
  have hH := hG.1 _ hmem
  have hL := liveCost_bound a r
  have h15c := h15.cost_le r
  have hPc := P.cost_le r layout.w layout.degree layout.C caps
  have hM : (rowMetadataWord layout.w layout.degree layout.C caps).length =
      2 * (RowsInit.metaWord layout.w layout.degree layout.C caps.headerFuel caps.copyCap caps.descriptorReserve
        caps.rawReserve).length + 1 := by
    rw [unwrap_meta, frame_length]
  have hS := RowsInit.small_pos a r
  have p1 : (r.smallSize a) ^ liveD a ≤ (r.smallSize a) ^ degOf selector a h15 P :=
    Nat.pow_le_pow_right hS (by unfold degOf; omega)
  have p2 : (r.smallSize a) ^ h15.degree ≤ (r.smallSize a) ^ degOf selector a h15 P :=
    Nat.pow_le_pow_right hS (by unfold degOf; omega)
  have p3 : (r.smallSize a) ^ P.degree ≤ (r.smallSize a) ^ degOf selector a h15 P :=
    Nat.pow_le_pow_right hS (by unfold degOf; omega)
  set X := (r.smallSize a) ^ degOf selector a h15 P + caps.headerFuel + layout.C + caps.copyCap +
    (rowMetadataWord layout.w layout.degree layout.C caps).length + 1 with hX
  have q1 : liveC a * (r.smallSize a) ^ liveD a ≤ liveC a * X := Nat.mul_le_mul_left _ (by omega)
  have q2 : h15.coefficient * (r.smallSize a) ^ h15.degree ≤ h15.coefficient * X := Nat.mul_le_mul_left _ (by omega)
  have q3 : P.coefficient * ((r.smallSize a) ^ P.degree + (rowMetadataWord layout.w layout.degree layout.C caps).length + 1)
      ≤ P.coefficient * X := Nat.mul_le_mul_left _ (by omega)
  have expand : coefOf selector a h15 P * X = 400 * X + liveC a * X + 2 * (h15.coefficient * X) + P.coefficient * X := by
    unfold coefOf
    ring
  unfold boundOf
  rw [← hX, expand]
  unfold costOf
  omega

/-! ## 3. The `HdrSpec` term -/

/-- **The rows Header writer**, as RX's `HdrSpec`: ONE fixed machine (from `a`, `h15`, `P`), its run for `Good` caps of every
nonempty family, and `cost_le` by definition. -/
def hdrSpecOf (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) : RowsInit.Hdr.HdrSpec selector a printer where
  needH := needH h15.extra P.extra
  states := _
  machine := machine selector a h15 P
  cost := fun r layout caps => boundOf selector a h15 P r layout caps
  coefficient := coefOf selector a h15 P
  degree := degOf selector a h15 P
  run := fun r layout facts caps hG hne => by
    obtain ⟨A', h, h1, h2, h3, h4, h5⟩ := run selector a h15 P r layout caps
    exact ⟨A', h.enlarge (costOf_le selector a printer h15 P r layout facts caps hG hne), h1, h2, h3, h4, h5⟩
  cost_le := fun _ _ _ => le_refl _

end
end RowsHeaderW
