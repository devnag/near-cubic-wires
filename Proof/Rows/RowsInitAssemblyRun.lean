import Proof.Rows.RowsInitAssemblyWork

/-! # Rows initializer: the `InitHole'` assembly, part 2 — the whole run to `Family.entry`'s blocks

**Consumer.** `InitHole'.initial` (`Proof/Rows/RowsFinalNE.lean`) and `InitHole'.c5` (`:50`): the final bank of ONE run of `initM` from
`rowPublicInput`, blockwise equal to `Family.entry`'s tapes (Header block `headerBank … 0`, Frame block `frameBank caps []`, work block
`workBank … (baseOf … at the bank's OWN pub/init/rcp) … 0`, counter `word |rows|`), heads `hFin`, and `C5Ready` on its `init` block
(nonempty families).

**Proof.** `work_run` (part 1) ; RX's `Global.work_dock` ; `tailIn_of` (the tail's entry facts from the work phase's `Side`, `baseOf`'s
`rowp` words and `rowPublicInput`) ; RX's `Global.tail_ne` / `tail_e` ; `TailOut.low` transports `C5Ready` (init ports `< 146 < iD`).

**Paper.** `paper.tex:1190-1212`.
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

/-! ## 1. Block facts -/

section Blocks
variable (a : DecompositionAlgorithm)

/-- `baseOf`'s `rowp` block is `rowpWords n` at every request (some arity `n`). -/
theorem baseOf_rowp (NI : ℕ) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool)
    (C cC hF : ℕ) (r : Request) (j : ℕ) :
    ∃ n, ∀ i, baseOf a NI pub init rcp C cC hF r j (rowpPort NI i) = rowpWords n C cC hF i := by
  cases r with
  | terminal => exact ⟨0, fun i => by simp only [baseOf, layout_rowp]⟩
  | thr r four L target => exact ⟨_, (thr_base_rc a r four L target NI pub init rcp C cC hF j).2.2.1⟩
  | sym r four L target => exact ⟨_, (sym_base_rc a r four L target NI pub init rcp C cC hF j).2.2.1⟩

theorem pub_ni (NI : ℕ) (j : Fin 2) : ∀ i, pubPort NI j ≠ initPort NI i :=
  not_init NI _ (by rw [RowsInit.ThrLoop.pub_val]; have := j.isLt; omega)

theorem rcp_ni (NI : ℕ) (j : Fin 64) : ∀ i, rcpPort NI j ≠ initPort NI i :=
  not_init NI _ (by rw [RowsInit.Prefix.rcp_val]; omega)

/-- **`C5Ready` reads the `init` block only below `146`.** -/
theorem c5_congr (NI : ℕ) (h : 146 ≤ NI) (init init' : Fin NI → List Bool) (Rp : ℕ) (r : Request)
    (he : ∀ i : Fin NI, i.val < 146 → init' i = init i)
    (hc : PartsStep.C5Ready a NI init (RowsInit.ThrInitReady.iMode NI h) (RowsInit.ThrInitReady.ini NI h)
      (RowsInit.ThrInitReady.ix NI h) (RowsInit.ThrInitReady.ib NI h) (RowsInit.ThrInitReady.iOne NI h)
      (RowsInit.ThrInitReady.iniS NI h) Rp r) :
    PartsStep.C5Ready a NI init' (RowsInit.ThrInitReady.iMode NI h) (RowsInit.ThrInitReady.ini NI h)
      (RowsInit.ThrInitReady.ix NI h) (RowsInit.ThrInitReady.ib NI h) (RowsInit.ThrInitReady.iOne NI h)
      (RowsInit.ThrInitReady.iniS NI h) Rp r := by
  have vM : (RowsInit.ThrInitReady.iMode NI h).val < 146 := by unfold RowsInit.ThrInitReady.iMode; simp only; omega
  have vI : ∀ m, (RowsInit.ThrInitReady.ini NI h m).val < 146 := fun m => by
    unfold RowsInit.ThrInitReady.ini; simp only; omega
  have vX : ∀ c, (RowsInit.ThrInitReady.ix NI h c).val < 146 := fun c => by
    unfold RowsInit.ThrInitReady.ix; simp only; omega
  have vB : ∀ k, (RowsInit.ThrInitReady.ib NI h k).val < 146 := fun k => by
    unfold RowsInit.ThrInitReady.ib; simp only; omega
  have vO : (RowsInit.ThrInitReady.iOne NI h).val < 146 := by unfold RowsInit.ThrInitReady.iOne; simp only; omega
  have vS : ∀ m, (RowsInit.ThrInitReady.iniS NI h m).val < 146 := fun m => by
    unfold RowsInit.ThrInitReady.iniS; simp only; omega
  cases r with
  | terminal => exact hc
  | thr r four L target =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hc
    exact ⟨(he _ vM).trans h1, h2, fun m => (he _ (vI m)).trans (h3 m), h4, h5, fun c => (he _ (vX c)).trans (h6 c),
      fun k hk => (he _ (vB k)).trans (h7 k hk), (he _ vO).trans h8⟩
  | sym r four L target =>
    obtain ⟨h1, h2⟩ := hc
    exact ⟨(he _ vM).trans h1, fun m => (he _ (vS m)).trans (h2 m)⟩

end Blocks

/-! ## 2. The tail's entry facts from the work phase -/

section Tail
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (H : RowsInit.Hdr.HdrSpec selector a printer)

theorem rq_val (w : ℕ) : (rowRequestPort printer w).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) := rfl
theorem rc_val (w : ℕ) : (rowCapsPort printer w).val = 440 + (P1TopDownPaidPayload.tapes printer + 2) + 1 := rfl

/-- `rowPublicInput` off the Header ports 0/262 and the two public work ports is blank. -/
theorem pub_blank (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) (NI : ℕ)
    (x : Fin (rowTapes printer (rowsWork NI) + 1)) (h0 : x.val ≠ 0) (h2 : x.val ≠ 262)
    (h3 : x.val ≠ 440 + (P1TopDownPaidPayload.tapes printer + 2)) (h4 : x.val ≠ 440 + (P1TopDownPaidPayload.tapes printer + 2) + 1) :
    rowPublicInput selector a printer (rowsWork NI) r layout caps x = [] := by
  have n1 : x ≠ rowRequestPort printer (rowsWork NI) := fun h => h3 (by rw [h, rq_val])
  have n2 : x ≠ rowCapsPort printer (rowsWork NI) := fun h => h4 (by rw [h, rc_val])
  simp only [rowPublicInput, h0, h2, n1, n2, if_false]

theorem tailIn_of (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (B : Fin (2 + rowsWork (NI a H.needH)) → List Bool)
    (hB : B = baseOf a (NI a H.needH) (fun i => B (pubPort (NI a H.needH) i)) (fun i => B (initPort (NI a H.needH) i))
      (fun i => B (rcpPort (NI a H.needH) i)) layout.C caps.copyCap caps.headerFuel r 0)
    (sd : RowsInit.WorkPhase.Side a (NI a H.needH) 150 (oT a H.needH) layout.w layout.degree layout.C caps.headerFuel
      caps.copyCap caps.descriptorReserve caps.rawReserve r B) :
    TailIn selector a printer (NI a H.needH) (iD a) H r layout caps
      (install (wS printer (NI a H.needH)) (rowPublicInput selector a printer (rowsWork (NI a H.needH)) r layout caps) B) := by
  obtain ⟨s0, s1, s40, s150, sbl⟩ := sd
  obtain ⟨n, hn⟩ := baseOf_rowp a (NI a H.needH) (fun i => B (pubPort (NI a H.needH) i)) (fun i => B (initPort (NI a H.needH) i))
    (fun i => B (rcpPort (NI a H.needH) i)) layout.C caps.copyCap caps.headerFuel r 0
  have hw : ∀ k, install (wS printer (NI a H.needH)) (rowPublicInput selector a printer (rowsWork (NI a H.needH)) r layout caps) B
      (wS printer (NI a H.needH) k) = B k := fun k => install_slot _ (wS_inj printer (NI a H.needH)) _ _ k
  have hrp : ∀ i, B (rowpPort (NI a H.needH) i) = rowpWords n layout.C caps.copyCap caps.headerFuel i :=
    fun i => (congrFun hB _).trans (hn i)
  have hlo : ∀ x : Fin (rowTapes printer (rowsWork (NI a H.needH)) + 1),
      x.val < 440 + (P1TopDownPaidPayload.tapes printer + 2) →
      install (wS printer (NI a H.needH)) (rowPublicInput selector a printer (rowsWork (NI a H.needH)) r layout caps) B x =
        rowPublicInput selector a printer (rowsWork (NI a H.needH)) r layout caps x := fun x hx =>
    install_other _ _ _ _ (fun j h => by have := congrArg Fin.val h; rw [wS_val] at this; omega)
  have hR' := hR a H.needH
  have hW := RowsInit.ThrLoop.rw_eq (NI a H.needH)
  refine ⟨fun k => ?_, fun k => ?_, ?_, (hw _).trans s0, (hw _).trans s1, ?_, ?_, ?_, ?_, (hw _).trans s40, (hw _).trans s150,
    fun x h1 h2 => ?_⟩
  · have hk := k.isLt
    have hv := hS_val printer (NI a H.needH) k
    rw [hlo _ (by rw [hv]; omega)]
    have n1 : RowsInit.Global.hS printer (NI a H.needH) k ≠ rowRequestPort printer (rowsWork (NI a H.needH)) := fun h => by
      have := congrArg Fin.val h; rw [hv, rq_val] at this; omega
    have n2 : RowsInit.Global.hS printer (NI a H.needH) k ≠ rowCapsPort printer (rowsWork (NI a H.needH)) := fun h => by
      have := congrArg Fin.val h; rw [hv, rc_val] at this; omega
    simp only [rowPublicInput, hv, n1, n2, if_false]
  · have hk := k.isLt
    have hv := fS_val printer (NI a H.needH) k
    rw [hlo _ (by rw [hv]; omega)]
    exact pub_blank selector a printer r layout caps _ _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)
  · rw [install_other _ _ _ _ (fun j h => by
      have := congrArg Fin.val h; rw [wS_val, cS_val] at this; have := j.isLt; omega)]
    have hv := cS_val printer (NI a H.needH)
    exact pub_blank selector a printer r layout caps _ _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)
  · rw [hw, hrp]; rfl
  · rw [hw, hrp]; rfl
  · rw [hw, hrp]; rfl
  · rw [hw, hrp]; rfl
  · simp only [wv] at h1 h2
    have hoT : oT a H.needH = iD a + 1 + eC a + 6 + H.needH := rfl
    have hx : x.val - (440 + (P1TopDownPaidPayload.tapes printer + 2)) < 2 + rowsWork (NI a H.needH) := by
      omega
    have ex : x = wS printer (NI a H.needH) ⟨x.val - (440 + (P1TopDownPaidPayload.tapes printer + 2)), hx⟩ :=
      Fin.ext (by rw [wS_val]; simp only; omega)
    rw [ex, hw]
    exact sbl _ (by simp only; unfold iD at h1; omega) (by simp only; rw [hoT]; omega)

end Tail

/-! ## 3. The whole run -/

section Run
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (H : RowsInit.Hdr.HdrSpec selector a printer)

/-- **What the final bank of the initializer satisfies** (all read at the bank itself: no chosen word is pinned from outside). -/
def Final (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (F : Fin (rowTapes printer (rowsWork (NI a H.needH)) + 1) → List Bool) : Prop :=
  Step (initM selector a printer H) (initCost selector a printer H r layout caps) (fun _ => 0)
      (rowPublicInput selector a printer (rowsWork (NI a H.needH)) r layout caps) (hFin printer (NI a H.needH)) F ∧
    (∀ k, F (RowsInit.Global.hS printer (NI a H.needH) k) = PCJ45bee56da9f34d5a_RowState.headerBank a (r.family a) (geometryOf selector a r)
      layout (PartsStep.reserveOf caps) 0 k) ∧
    F (cS printer (NI a H.needH)) = RepairSource.VerifierDecoding.CompareMachine.word (r.family a).rows.length ∧
    (∀ k, F (fS printer (NI a H.needH) k) = if k.val = P1TopDownPaidPayload.tapes printer then
      List.replicate caps.descriptorReserve false else List.replicate caps.copyCap false) ∧
    (∀ x, F (wS printer (NI a H.needH) x) = PCJ45bee56da9f34d5a_RowState.workBank (rowsWork (NI a H.needH)) caps
      (baseOf a (NI a H.needH) (fun i => F (wS printer (NI a H.needH) (pubPort (NI a H.needH) i)))
        (fun i => F (wS printer (NI a H.needH) (initPort (NI a H.needH) i)))
        (fun i => F (wS printer (NI a H.needH) (rcpPort (NI a H.needH) i))) layout.C caps.copyCap caps.headerFuel r)
      (rowpPort (NI a H.needH) 0) (rowpPort (NI a H.needH) 1) 0 x) ∧
    ((r.family a).rows ≠ [] →
      PartsStep.C5Ready a (NI a H.needH) (fun i => F (wS printer (NI a H.needH) (initPort (NI a H.needH) i)))
        (RowsInit.ThrInitReady.iMode (NI a H.needH) (h146 a H.needH)) (RowsInit.ThrInitReady.ini (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.ix (NI a H.needH) (h146 a H.needH)) (RowsInit.ThrInitReady.ib (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.iOne (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.iniS (NI a H.needH) (h146 a H.needH)) (PrimeReserve.rpOf a r) r)

/-- The work block and `C5Ready` after the tail, from the work phase's bank. -/
theorem work_block (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (B : Fin (2 + rowsWork (NI a H.needH)) → List Bool)
    (hB : B = baseOf a (NI a H.needH) (fun i => B (pubPort (NI a H.needH) i)) (fun i => B (initPort (NI a H.needH) i))
      (fun i => B (rcpPort (NI a H.needH) i)) layout.C caps.copyCap caps.headerFuel r 0)
    (c5B : (r.family a).rows ≠ [] →
      PartsStep.C5Ready a (NI a H.needH) (fun i => B (initPort (NI a H.needH) i))
        (RowsInit.ThrInitReady.iMode (NI a H.needH) (h146 a H.needH)) (RowsInit.ThrInitReady.ini (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.ix (NI a H.needH) (h146 a H.needH)) (RowsInit.ThrInitReady.ib (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.iOne (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.iniS (NI a H.needH) (h146 a H.needH)) (PrimeReserve.rpOf a r) r)
    (F : Fin (rowTapes printer (rowsWork (NI a H.needH)) + 1) → List Bool)
    (tout : TailOut selector a printer (NI a H.needH) (iD a) r layout caps
      (install (wS printer (NI a H.needH)) (rowPublicInput selector a printer (rowsWork (NI a H.needH)) r layout caps) B) F) :
    (∀ x, F (wS printer (NI a H.needH) x) = PCJ45bee56da9f34d5a_RowState.workBank (rowsWork (NI a H.needH)) caps
      (baseOf a (NI a H.needH) (fun i => F (wS printer (NI a H.needH) (pubPort (NI a H.needH) i)))
        (fun i => F (wS printer (NI a H.needH) (initPort (NI a H.needH) i)))
        (fun i => F (wS printer (NI a H.needH) (rcpPort (NI a H.needH) i))) layout.C caps.copyCap caps.headerFuel r)
      (rowpPort (NI a H.needH) 0) (rowpPort (NI a H.needH) 1) 0 x) ∧
    ((r.family a).rows ≠ [] →
      PartsStep.C5Ready a (NI a H.needH) (fun i => F (wS printer (NI a H.needH) (initPort (NI a H.needH) i)))
        (RowsInit.ThrInitReady.iMode (NI a H.needH) (h146 a H.needH)) (RowsInit.ThrInitReady.ini (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.ix (NI a H.needH) (h146 a H.needH)) (RowsInit.ThrInitReady.ib (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.iOne (NI a H.needH) (h146 a H.needH))
        (RowsInit.ThrInitReady.iniS (NI a H.needH) (h146 a H.needH)) (PrimeReserve.rpOf a r) r) := by
  have hw : ∀ k, install (wS printer (NI a H.needH)) (rowPublicInput selector a printer (rowsWork (NI a H.needH)) r layout caps) B
      (wS printer (NI a H.needH) k) = B k := fun k => install_slot _ (wS_inj printer (NI a H.needH)) _ _ k
  have fw : ∀ x : Fin (2 + rowsWork (NI a H.needH)), (∀ i, x ≠ initPort (NI a H.needH) i) →
      F (wS printer (NI a H.needH) x) = B x := fun x hx => (tout.work x hx).trans (hw x)
  obtain ⟨n, hn⟩ := baseOf_rowp a (NI a H.needH) (fun i => B (pubPort (NI a H.needH) i)) (fun i => B (initPort (NI a H.needH) i))
    (fun i => B (rcpPort (NI a H.needH) i)) layout.C caps.copyCap caps.headerFuel r 0
  have hrp : ∀ i, B (rowpPort (NI a H.needH) i) = rowpWords n layout.C caps.copyCap caps.headerFuel i :=
    fun i => (congrFun hB _).trans (hn i)
  refine ⟨fun x => ?_, fun hne => c5_congr a (NI a H.needH) (h146 a H.needH) _ _ _ r (fun i hi => ?_) (c5B hne)⟩
  · by_cases hx : ∃ i, x = initPort (NI a H.needH) i
    · obtain ⟨i, rfl⟩ := hx
      unfold PCJ45bee56da9f34d5a_RowState.workBank
      rw [if_neg (fun h => rowp_ni (NI a H.needH) 0 i h.symm), if_neg (fun h => rowp_ni (NI a H.needH) 1 i h.symm), baseOf_init]
    · simp only [not_exists] at hx
      rw [fw x hx]
      unfold PCJ45bee56da9f34d5a_RowState.workBank
      by_cases h0 : x = rowpPort (NI a H.needH) 0
      · rw [if_pos h0, h0, hrp]; rfl
      rw [if_neg h0]
      by_cases h1 : x = rowpPort (NI a H.needH) 1
      · rw [if_pos h1, h1, hrp]; rfl
      rw [if_neg h1]
      by_cases hp : ∃ i, x = pubPort (NI a H.needH) i
      · obtain ⟨i, rfl⟩ := hp
        rw [baseOf_pub]
        exact (fw _ (pub_ni _ i)).symm
      by_cases hr : ∃ i, x = rcpPort (NI a H.needH) i
      · obtain ⟨i, rfl⟩ := hr
        rw [baseOf_rcp]
        exact (fw _ (rcp_ni _ i)).symm
      simp only [not_exists] at hp hr
      rw [congrFun hB x]
      exact baseOf_indep a (NI a H.needH) _ _ _ _ _ _ layout.C caps.copyCap caps.headerFuel r 0 x hp hx hr
  · rw [tout.low i (by unfold iD; omega), hw]

/-- **The whole run** from `rowPublicInput` to the final bank, at `Good` caps. -/
theorem final_run (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps)
    (good : RowCaps.Good selector a printer r layout facts caps) :
    ∃ F, Final selector a printer H r layout caps F := by
  obtain ⟨B, sW, eB, c5B, sd⟩ := work_run selector a H.needH r layout.w layout.degree layout.C caps.headerFuel caps.copyCap
    caps.descriptorReserve caps.rawReserve
  have dW := work_dock selector a printer (NI a H.needH) r layout caps sW
  have tin := tailIn_of selector a printer H r layout caps B eB sd
  by_cases he : (r.family a).rows = []
  · obtain ⟨F, sT, hh, tout⟩ := tail_e selector a printer (NI a H.needH) (iD a) (hI a H.needH) H (hR a H.needH) (hD a) r layout
      caps he _ tin
    obtain ⟨wb, c5⟩ := work_block selector a printer H r layout caps B eB c5B F tout
    refine ⟨F, (dW.seq sT).enlarge (by unfold initCost; omega), fun k => ?_, tout.ctr, tout.frm, wb, c5⟩
    rw [hh k, PCJ45bee56da9f34d5a_RowState.headerBank, if_pos he]
    by_cases h0 : k.val = 0
    · rw [if_pos h0, if_pos (Fin.ext h0)]
    · rw [if_neg h0, if_neg (fun h => h0 (by rw [h]; rfl))]
  · obtain ⟨F, sT, hh, tout⟩ := tail_ne selector a printer (NI a H.needH) (iD a) (hI a H.needH) H (hR a H.needH) (hD a) r layout
      facts caps good he _ tin
    obtain ⟨wb, c5⟩ := work_block selector a printer H r layout caps B eB c5B F tout
    refine ⟨F, (dW.seq sT).enlarge (by unfold initCost; omega), fun k => ?_, tout.ctr, tout.frm, wb, c5⟩
    rw [hh k, PCJ45bee56da9f34d5a_RowState.headerBank, if_neg he]

/-- A `C5Ready` init block at every request (the work phase's; used off `Good`). -/
theorem c5_wit (r : Request) : ∃ init : Fin (NI a H.needH) → List Bool, (r.family a).rows ≠ [] →
    PartsStep.C5Ready a (NI a H.needH) init
      (RowsInit.ThrInitReady.iMode (NI a H.needH) (h146 a H.needH)) (RowsInit.ThrInitReady.ini (NI a H.needH) (h146 a H.needH))
      (RowsInit.ThrInitReady.ix (NI a H.needH) (h146 a H.needH)) (RowsInit.ThrInitReady.ib (NI a H.needH) (h146 a H.needH))
      (RowsInit.ThrInitReady.iOne (NI a H.needH) (h146 a H.needH))
      (RowsInit.ThrInitReady.iniS (NI a H.needH) (h146 a H.needH)) (PrimeReserve.rpOf a r) r := by
  obtain ⟨B, -, -, c5B, -⟩ := work_run selector a H.needH r 0 0 0 0 0 0 0
  exact ⟨_, c5B⟩

end Run

end
end RowsConstruction.InitAssembly
