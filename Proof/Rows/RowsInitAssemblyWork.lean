import Proof.Rows.RowsFinalNE
import Proof.Rows.RowsFrameSymCost
import Proof.Rows.RowsFrameThrBnd
import Proof.Rows.RowsInitGlobal

/-! # Rows initializer: the `InitHole'` assembly, part 1 — offsets, the machine, the work phase at every request, the cost

**Consumer.** `RowsConstruction.FinalNE.InitHole' selector a printer (PrimeReserve.rpOf a)` (`Proof/Rows/RowsFinalNE.lean`), whose `initial`
is `Parts.initial`'s exact entry: ONE machine on `Fin (rowTapes printer (rowsWork NI) + 1)` from `rowPublicInput` (heads `0`) to
`Family.entry`'s heads and tapes within `rowInitBudget`, and whose `c5` is `C5Ready` on the SAME `init` block (nonempty families).

**Machine** `initM` = RX's work phase `WorkPhase.workM` docked on the work slots (`Global.work_dock`) ; RX's global tail
`Global.tailM` (Frame writer ; family counter ; Header writer | Header-277 bump). SYM branch: RF's `FrameSymInst.symSpec`; THR cascade
bounds: RF's `FrameThrBnd.thrBnd/thrBndW`; the Header writer `H : HdrSpec` (RH) is the one typed input.

**Offsets** (fixed per `a`, `H.needH`): prefix scratch from `150`, the tail's scratch `[iD, oT)` inside the work phase's blank region
`[150 + needP, oT)` (`WorkPhase.Side`), THR branch regions from `oT`, SYM branch from `oT`.

**Paper.** `paper.tex:1190-1212` (per-request initialization: the public request and caps in, every request constant computed).
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsConstruction.InitAssembly
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.PacketFamilyParent
open RowsInit.Global
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. Offsets -/

section Offsets
variable (a : DecompositionAlgorithm) (nH : ℕ)

/-- The tail's scratch start (the Frame writer's log port). -/
def iD : ℕ := 150 + RowsInit.Prefix.needP a
/-- The branch region start (THR init words, SYM branch). -/
def oT : ℕ := iD a + 1 + eC a + 6 + nH
/-- The THR loop-block scratch start. -/
def oI : ℕ := oT a nH + RowsInit.ThrInitRun.need a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a)
  ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU
/-- The THR C5 scratch start. -/
def oC : ℕ := oI a nH + RowsInit.ThrLoop.need a
/-- **The init block's size.** -/
def NI : ℕ := max (oC a nH + RowsInit.C5.needC a)
  (oT a nH + RowsInit.FrameSymWork.needS a (RowsInit.FrameSymInst.symLoop a))

theorem h146 : 146 ≤ NI a nH := by unfold NI oC oI oT iD; omega
theorem hB : 150 ≤ oT a nH := by unfold oT iD; omega
theorem hS : oT a nH + RowsInit.FrameSymWork.needS a (RowsInit.FrameSymInst.symLoop a) ≤ NI a nH := by
  unfold NI; omega
theorem hP : 150 + RowsInit.Prefix.needP a ≤ oT a nH := by unfold oT iD; omega
theorem hTo : oT a nH + RowsInit.ThrInitRun.need a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a)
    ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU ≤ oI a nH := le_refl _
theorem hNo : oI a nH + RowsInit.ThrLoop.need a ≤ oC a nH := le_refl _
theorem hC : oC a nH + RowsInit.C5.needC a ≤ NI a nH := by unfold NI; omega
theorem hI : iD a < NI a nH := by unfold NI oC oI oT; omega
theorem hR : iD a + 1 + eC a + 6 + nH ≤ NI a nH := by unfold NI oC oI oT; omega
theorem hD : 150 ≤ iD a := by unfold iD; omega

end Offsets

/-! ## 2. The machines -/

section Machines
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (H : RowsInit.Hdr.HdrSpec selector a printer)

/-- RF's SYM branch at the offsets. -/
abbrev symS (nH : ℕ) : RowsInit.WorkPhase.SymSpec a (NI a nH) (oT a nH) (h146 a nH) :=
  RowsInit.FrameSymInst.symSpec a (NI a nH) (oT a nH) (h146 a nH) (hB a nH) (hS a nH)

/-- The work phase (RX), at RF's THR bounds and SYM branch. -/
abbrev workM (nH : ℕ) := RowsInit.WorkPhase.workM a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a)
  (NI a nH) 150 (oT a nH) (oI a nH) (oC a nH) (h146 a nH) (symS a nH)

/-- **The initializer**: the work phase on the work slots ; the global tail. -/
def initM := Composition.machine (RecoveryFocus.machine (wS printer (NI a H.needH)) (workM a H.needH))
  (tailM selector a printer (NI a H.needH) (iD a) (hI a H.needH) H)

end Machines

/-! ## 3. The work phase at every request -/

section Work
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
include selector in

theorem arity_thr (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ) :
    RowsInit.Prefix.arityOf a (.thr r four L target) = thrN a r L target := by
  have h := PartsStep.residual_eq (Packets.thrFamily a r L target) (Packets.geometry selector _)
  show (Packets.live (Packets.thrFamily a r L target))ᶜ.card * 1 =
    (Packets.residual (Packets.thrFamily a r L target) + 1) / 2 + Packets.residual (Packets.thrFamily a r L target) / 2
  rw [← h]
  omega

include selector in
theorem arity_sym (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ) :
    RowsInit.Prefix.arityOf a (.sym r four L target) = symN r L target := by
  have h := PartsStep.residual_eq (Packets.symFamily r L target) (Packets.geometry selector _)
  show (Packets.live (Packets.symFamily r L target))ᶜ.card * 1 =
    (Packets.residual (Packets.symFamily r L target) + 1) / 2 + Packets.residual (Packets.symFamily r L target) / 2
  rw [← h]
  omega

/-- The taken branch's cost (before the two switches). -/
def brCost : Request → ℕ
  | .terminal => 0
  | .thr r four L target => if 0 < (Packets.thrFamily a r L target).rows.length then
      RowsInit.ThrWork.neCost a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a) r four L target else 0
  | .sym r four L target => if 0 < (Packets.symFamily r L target).rows.length then
      RowsInit.FrameSymWork.neCost a (RowsInit.FrameSymInst.symLoop a) (.sym r four L target) + 2 else 2

/-- The work phase's cost. -/
def workCost (r : Request) (w deg C hF cC dR rR : ℕ) : ℕ :=
  RowsInit.Prefix.cost a r w deg C hF cC dR rR + 1 + (brCost a r + 2 + 2)

variable (nH : ℕ)

include selector in
/-- **The work phase at every request**: `base 0` at the bank's own blocks, `C5Ready` on a nonempty family, and `Side`. -/
theorem work_run (r : Request) (w deg C hF cC dR rR : ℕ) :
    ∃ B : Fin (2 + rowsWork (NI a nH)) → List Bool,
      Step (workM a nH) (workCost a r w deg C hF cC dR rR) (fun _ => 0)
        (RowsInit.WorkPhase.workIn (NI a nH) (frame (r.input a)) (frame (RowsInit.metaWord w deg C hF cC dR rR)))
        (fun _ => 0) B ∧
      B = baseOf a (NI a nH) (fun i => B (pubPort (NI a nH) i)) (fun i => B (initPort (NI a nH) i))
        (fun i => B (rcpPort (NI a nH) i)) C cC hF r 0 ∧
      ((r.family a).rows ≠ [] →
        PartsStep.C5Ready a (NI a nH) (fun i => B (initPort (NI a nH) i)) (RowsInit.ThrInitReady.iMode (NI a nH) (h146 a nH))
          (RowsInit.ThrInitReady.ini (NI a nH) (h146 a nH)) (RowsInit.ThrInitReady.ix (NI a nH) (h146 a nH))
          (RowsInit.ThrInitReady.ib (NI a nH) (h146 a nH)) (RowsInit.ThrInitReady.iOne (NI a nH) (h146 a nH))
          (RowsInit.ThrInitReady.iniS (NI a nH) (h146 a nH)) (PrimeReserve.rpOf a r) r) ∧
      RowsInit.WorkPhase.Side a (NI a nH) 150 (oT a nH) w deg C hF cC dR rR r B := by
  have hw := fun (h1 : 150 ≤ 150) => RowsInit.WorkPhase.term a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a)
    (NI a nH) 150 (oT a nH) (oI a nH) (oC a nH) (h146 a nH) (symS a nH) h1 (hP a nH) (hTo a nH) (hNo a nH) (hC a nH)
    w deg C hF cC dR rR
  cases r with
  | terminal =>
    obtain ⟨B, s, e, sd⟩ := hw le_rfl
    exact ⟨B, s, e, fun _ => trivial, sd⟩
  | thr r four L target =>
    by_cases hne : 0 < (Packets.thrFamily a r L target).rows.length
    · obtain ⟨B, s, e, c5, sd⟩ := RowsInit.WorkPhase.thr_ne a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a)
        (NI a nH) 150 (oT a nH) (oI a nH) (oC a nH) (h146 a nH) (symS a nH) le_rfl (hP a nH) (hTo a nH) (hNo a nH) (hC a nH)
        w deg C hF cC dR rR r four L target (arity_thr selector a r four L target)
        (RowsInit.FrameThrBnd.thrBnd_eq a r four L target) hne
      refine ⟨B, ?_, e, fun _ => c5, sd⟩
      have hc : workCost a (.thr r four L target) w deg C hF cC dR rR = RowsInit.Prefix.cost a (.thr r four L target) w deg C
          hF cC dR rR + 1 + (RowsInit.ThrWork.neCost a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a) r four
            L target + 2 + 2) := by simp only [workCost, brCost, if_pos hne]
      rw [hc]
      exact s
    · obtain ⟨B, s, e, sd⟩ := RowsInit.WorkPhase.thr_e a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a)
        (NI a nH) 150 (oT a nH) (oI a nH) (oC a nH) (h146 a nH) (symS a nH) le_rfl (hP a nH) (hTo a nH) (hNo a nH) (hC a nH)
        w deg C hF cC dR rR r four L target (arity_thr selector a r four L target) (by omega)
      refine ⟨B, ?_, e, fun h => absurd (List.length_pos_iff.mpr h) hne, sd⟩
      have hc : workCost a (.thr r four L target) w deg C hF cC dR rR = RowsInit.Prefix.cost a (.thr r four L target) w deg C
          hF cC dR rR + 1 + (0 + 2 + 2) := by simp only [workCost, brCost, if_neg hne]
      rw [hc]
      exact s
  | sym r four L target =>
    by_cases hne : 0 < (Packets.symFamily r L target).rows.length
    · obtain ⟨B, s, e, c5, sd⟩ := RowsInit.WorkPhase.sym_ne a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a)
        (NI a nH) 150 (oT a nH) (oI a nH) (oC a nH) (h146 a nH) (symS a nH) le_rfl (hP a nH) (hTo a nH) (hNo a nH) (hC a nH)
        w deg C hF cC dR rR r four L target (arity_sym selector a r four L target) hne
      refine ⟨B, ?_, e, fun _ => c5, sd⟩
      have hc : workCost a (.sym r four L target) w deg C hF cC dR rR = RowsInit.Prefix.cost a (.sym r four L target) w deg C
          hF cC dR rR + 1 + ((symS a nH).costNe (.sym r four L target) + 2 + 2) := by
        simp only [workCost, brCost, if_pos hne, symS, RowsInit.FrameSymCost.costNe_eq]
      rw [hc]
      exact s
    · obtain ⟨B, s, e, sd⟩ := RowsInit.WorkPhase.sym_e a (RowsInit.FrameThrBnd.thrBnd a) (RowsInit.FrameThrBnd.thrBndW a)
        (NI a nH) 150 (oT a nH) (oI a nH) (oC a nH) (h146 a nH) (symS a nH) le_rfl (hP a nH) (hTo a nH) (hNo a nH) (hC a nH)
        w deg C hF cC dR rR r four L target (arity_sym selector a r four L target) (by omega)
      refine ⟨B, ?_, e, fun h => absurd (List.length_pos_iff.mpr h) hne, sd⟩
      have hc : workCost a (.sym r four L target) w deg C hF cC dR rR = RowsInit.Prefix.cost a (.sym r four L target) w deg C
          hF cC dR rR + 1 + ((symS a nH).costE (.sym r four L target) + 2 + 2) := by
        simp only [workCost, brCost, if_neg hne, symS, RowsInit.FrameSymCost.costE_eq]
      rw [hc]
      exact s

end Work

/-! ## 4. The initializer's cost (one uniform bound for both tail branches) -/

section Cost
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (H : RowsInit.Hdr.HdrSpec selector a printer)

/-- **The initializer's charged cost**: the work phase, the composition step, and the tail (Header-writer branch; the bump branch
costs `headCost + 3`, below it). -/
def initCost (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) : ℕ :=
  workCost a r layout.w layout.degree layout.C caps.headerFuel caps.copyCap caps.descriptorReserve caps.rawReserve + 1 +
    (headCost a r caps + (H.cost r layout caps + 2) + 3)

end Cost

end
end RowsConstruction.InitAssembly
