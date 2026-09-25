import Proof.Rows.RowsInitCostParts
import Proof.Rows.RowsInitAssemblyWork

/-! # Rows initializer: the WHOLE initializer's cost fits `rowInitBudget` (RW's `InitHole'.initial` budget)

**Consumer.** `RowsConstruction.FinalNE.InitHole'.initial : Step initializer (rowInitBudget a coefficient degree r layout.w layout.degree
layout.C caps) …` (`Proof/Rows/RowsFinalNE.lean`), through RW's `RowsConstruction.InitAssembly.initCost selector a printer H r layout caps`
(`Proof/Rows/RowsInitAssemblyWork.lean`: the work phase `workCost` ; the composition step ; the global tail `headCost + (H.cost + 2) + 3`).

**Result.** **`init_cost_le selector a printer H : ∃ K D, ∀ r layout caps, initCost selector a printer H r layout caps ≤
rowInitBudget a K D r layout.w layout.degree layout.C caps`** — the constants depend only on `a` and the Header writer `H`
(fixed before any request, `paper.tex:4280-4290`).

**Ingredients (all verified, by name).** RS's `InitCost.prefix_cost_le`, `InitCost.thr_ne_cost_le` (at RF's `FrameThrBnd.thrBnd/thrBndW`),
RF's `FrameSymCost.sym_cost_exists`, RX's `FamilyWord.wordCost_small (Global.ctrS a)`, RH's `H.cost_le`, `Global.meta_eq`
(`|metaWord| ≤ |rowMetadataWord|`). Classes (R-C): the only `2^residual·(q+|input|+1)^D` summand is the branch's loop-block table
stage; every other summand is a fixed power of `smallSize` or linear in `headerFuel, C, copyCap, descriptorReserve, |metadata|`,
all inside `rowInitBudget`; nothing small-class multiplies the table factor.

**Paper.** `paper.tex:1102-1112`, `:1190-1233`. **Budget.** This module is the accounting.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.CostTotal
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-- Raising coefficient and degree of an `RB`-shaped bound. -/
theorem rb_mono (c c' d d' S Y0 m : ℕ) (hc : c ≤ c') (hd : d ≤ d') (hS : 1 ≤ S) (hm : 1 ≤ m) :
    c * (S ^ d + Y0 * m ^ d + 1) ≤ c' * (S ^ d' + Y0 * m ^ d' + 1) := by
  have h1 := Nat.pow_le_pow_right hS hd
  have h2 := Nat.mul_le_mul_left Y0 (Nat.pow_le_pow_right hm hd)
  exact Nat.mul_le_mul hc (by omega)

/-- **The taken branch** (`InitAssembly.brCost`: THR / SYM, empty or not, terminal) in `RB` form. -/
theorem br_le (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) :
    ∃ c d : ℕ, ∀ r : Request, InitAssembly.brCost a r ≤
      c * ((r.smallSize a) ^ d + 2 ^ Packets.residual (r.family a) * (r.q + (r.input a).length + 1) ^ d + 1) := by
  obtain ⟨cT, dT, hT⟩ := RowsInit.InitCost.thr_ne_cost_le selector a (RowsInit.FrameThrBnd.thrBnd a)
    (RowsInit.FrameThrBnd.thrBndW a)
  obtain ⟨cS, dS, hS⟩ := RowsInit.FrameSymCost.sym_cost_exists selector a
  refine ⟨cT + cS + 2, dT + dS, fun r => ?_⟩
  cases r with
  | terminal => simp [InitAssembly.brCost]
  | thr r four L target =>
    have hS1 : 1 ≤ (Request.thr r four L target).smallSize a := one_le_small a _
    have hm1 : 1 ≤ (Request.thr r four L target).q + ((Request.thr r four L target).input a).length + 1 := by omega
    simp only [InitAssembly.brCost]
    split_ifs
    · exact le_trans (hT r four L target) (rb_mono _ _ _ _ _ _ _ (by omega) (by omega) hS1 hm1)
    · exact Nat.zero_le _
  | sym r four L target =>
    have hS1 : 1 ≤ (Request.sym r four L target).smallSize a := one_le_small a _
    have hm1 : 1 ≤ (Request.sym r four L target).q + ((Request.sym r four L target).input a).length + 1 := by omega
    simp only [InitAssembly.brCost]
    split_ifs
    · exact le_trans (hS r four L target) (rb_mono _ _ _ _ _ _ _ (by omega) (by omega) hS1 hm1)
    · have h1 : 1 ≤ (Request.sym r four L target).smallSize a ^ (dT + dS) := Nat.one_le_pow _ _ hS1
      have h2 : 2 * 1 ≤ 2 * ((Request.sym r four L target).smallSize a ^ (dT + dS) +
          2 ^ Packets.residual ((Request.sym r four L target).family a) *
            ((Request.sym r four L target).q + ((Request.sym r four L target).input a).length + 1) ^ (dT + dS) + 1) :=
        Nat.mul_le_mul_left 2 (by omega)
      exact le_trans (by omega) (le_trans h2 (Nat.mul_le_mul_right _ (by omega)))

/-- **The whole initializer's cost fits `rowInitBudget`** (RW's `InitAssembly.initCost`). -/
theorem init_cost_le (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (H : RowsInit.Hdr.HdrSpec selector a printer) :
    ∃ K D : ℕ, ∀ (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps),
      InitAssembly.initCost selector a printer H r layout caps ≤
        rowInitBudget a K D r layout.w layout.degree layout.C caps := by
  obtain ⟨cP, dP, hP⟩ := RowsInit.InitCost.prefix_cost_le a
  obtain ⟨cB, dB, hB⟩ := br_le selector a
  obtain ⟨cW, dW, hW⟩ := RowsInit.FamilyWord.wordCost_small (RowsInit.Global.ctrS a)
  refine ⟨cP + cB + cW + H.coefficient + 32, dP + dB + dW + H.degree, fun r layout caps => ?_⟩
  have hS1 : 1 ≤ r.smallSize a := one_le_small a r
  have hm1 : 1 ≤ r.q + (r.input a).length + 1 := by omega
  have hmeta : (RowsInit.metaWord layout.w layout.degree layout.C caps.headerFuel caps.copyCap caps.descriptorReserve
      caps.rawReserve).length ≤ (rowMetadataWord layout.w layout.degree layout.C caps).length := by
    rw [RowsInit.Global.meta_eq, frame_length]; omega
  have hPre := hP r layout.w layout.degree layout.C caps.headerFuel caps.copyCap caps.descriptorReserve caps.rawReserve
  have hBr := hB r
  have hWd := hW r
  have hH := H.cost_le r layout caps
  have pP : (r.smallSize a) ^ dP ≤ (r.smallSize a) ^ (dP + dB + dW + H.degree) := Nat.pow_le_pow_right hS1 (by omega)
  have pB : (r.smallSize a) ^ dB ≤ (r.smallSize a) ^ (dP + dB + dW + H.degree) := Nat.pow_le_pow_right hS1 (by omega)
  have pW : (r.smallSize a) ^ dW ≤ (r.smallSize a) ^ (dP + dB + dW + H.degree) := Nat.pow_le_pow_right hS1 (by omega)
  have pH : (r.smallSize a) ^ H.degree ≤ (r.smallSize a) ^ (dP + dB + dW + H.degree) := Nat.pow_le_pow_right hS1 (by omega)
  have pY : 2 ^ Packets.residual (r.family a) * (r.q + (r.input a).length + 1) ^ dB ≤
      2 ^ Packets.residual (r.family a) * (r.q + (r.input a).length + 1) ^ (dP + dB + dW + H.degree) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm1 (by omega))
  set Sig := (r.smallSize a) ^ (dP + dB + dW + H.degree) + caps.headerFuel + layout.C + caps.copyCap +
    caps.descriptorReserve + (rowMetadataWord layout.w layout.degree layout.C caps).length +
    2 ^ Packets.residual (r.family a) * (r.q + (r.input a).length + 1) ^ (dP + dB + dW + H.degree) + 1 with hSig
  have q1 : RowsInit.Prefix.cost a r layout.w layout.degree layout.C caps.headerFuel caps.copyCap caps.descriptorReserve
      caps.rawReserve ≤ cP * Sig := le_trans hPre (Nat.mul_le_mul_left _ (by omega))
  have q2 : InitAssembly.brCost a r ≤ cB * Sig := le_trans hBr (Nat.mul_le_mul_left _ (by omega))
  have q3 : RowsInit.FamilyWord.wordCost (RowsInit.Global.ctrS a) r ≤ cW * Sig :=
    le_trans hWd (Nat.mul_le_mul_left _ (by omega))
  have q4 : H.cost r layout caps ≤ H.coefficient * Sig := le_trans hH (Nat.mul_le_mul_left _ (by omega))
  have e : (cP + cB + cW + H.coefficient + 32) * Sig =
      cP * Sig + cB * Sig + cW * Sig + H.coefficient * Sig + 32 * Sig := by ring
  have hSig1 : 1 ≤ Sig := by omega
  calc InitAssembly.initCost selector a printer H r layout caps ≤ (cP + cB + cW + H.coefficient + 32) * Sig := by
        unfold InitAssembly.initCost InitAssembly.workCost RowsInit.Global.headCost
        rw [e]
        omega
    _ ≤ rowInitBudget a (cP + cB + cW + H.coefficient + 32) (dP + dB + dW + H.degree) r layout.w layout.degree layout.C
        caps := by
        unfold rowInitBudget rowBudget
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left _ (by omega)

end
end RowsInit.CostTotal
