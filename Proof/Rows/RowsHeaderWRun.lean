import Proof.Rows.RowsHeaderWBase

/-! # Rows Header writer, part 2: ONE fixed machine writing the entry Header bank

**Consumer.** `RowsInit.Hdr.HdrSpec.run` (`rows-rowlevel-20260923/RowsInitHdrSpec.lean`): from `hdrIn` (Header 0 = pool word,
262 = raw word, 440 framed request, 441 metadata word, 442/443 reserve driver/log, all else blank, heads `0`) to
`pad (PartsStep.reserveOf caps k) (RowState.commonHeader … k)` on every Header port `k`, with head `1` on Header 277 only and the
four public ports kept. Six docked stages, composed by `Step.seq`:
1. `unwrap_run` (441 → the unwrapped metadata word on scratch 444);
2. `RowsInit.live_chain` (73 ports): Header 3 = `tape n`, 283 = `tape (K+1)`, 277 = `word (2^K)` at head `1`;
3. `RowsInit.hdr_dock` (30 ports): Header 4 = `tape N`, 278 = `1^|pool word|`, 88 = `1^w`;
4. Header 15: RW's `header15Stage` (typed `h15`) under the all-heads masked reset;
5. Header 282: `H282Spec` (typed `P`; RH builds it next);
6. `RowsInit.reserves_step`: the 430 mutable Header ports `pad (2·headerFuel) []` from drv 442 / log 443.
Header 0 and 262 stay as given (`reserve 0`; `common_words`, `common_262`).

**Paper.** `paper.tex:1190-1212` (the Header block is prepared once per request). **Budget.** `costOf` = the six stage costs
plus five junction steps; bounded in `RowsHeaderWSpecOf` by `rowInitBudget`'s `smallSize^degree`, `headerFuel` and metadata terms.
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

/-! ## 1. Refined ranges -/

theorem lMap_nz (i : ℕ) (hi : i < 73) (h0 : i ≠ 0) :
    lMap i = 3 ∨ lMap i = 283 ∨ lMap i = 277 ∨ (446 ≤ lMap i ∧ lMap i ≤ 517) := by
  unfold lMap; split_ifs <;> omega
theorem lMap_277 (i : ℕ) (hi : i < 73) : lMap i = 277 ↔ i = 71 := by
  unfold lMap; split_ifs <;> omega
theorem aMap_ge3 (i : ℕ) (hi : i < 30) (h : 3 ≤ i) :
    aMap i = 4 ∨ aMap i = 278 ∨ aMap i = 88 ∨ (518 ≤ aMap i ∧ aMap i ≤ 544) := by
  unfold aMap; split_ifs <;> omega
theorem fMap_nz (e i : ℕ) (hi : i < 2 + e + 1) (h : i ≠ 0) : fMap i = 15 ∨ (545 ≤ fMap i ∧ fMap i ≤ 545 + e) := by
  unfold fMap; split_ifs <;> omega
theorem pMap_ge3 (e p i : ℕ) (hi : i < 4 + p) (h : 3 ≤ i) :
    pMap e i = 282 ∨ (546 + e ≤ pMap e i ∧ pMap e i ≤ 545 + e + p) := by
  unfold pMap; split_ifs <;> omega

/-- The public entry is blank off its six ports. -/
def Fresh (v : ℕ) : Prop := v ≠ 0 ∧ v ≠ 262 ∧ (v < 440 ∨ 443 < v)

theorem hdrIn_blank (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (nH : ℕ) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) (x : Fin (440 + 4 + nH))
    (hx : Fresh x.val) : RowsInit.Hdr.hdrIn selector a nH r layout caps x = [] := by
  unfold Fresh at hx
  unfold RowsInit.Hdr.hdrIn
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)

/-! ## 2. The machine and its cost -/

def stU (e p : ℕ) :=
  RecoveryFocus.machine (slU e p) (MaskedReset.machine GeneratedAmplifier.Copy.machine (fun _ => true))
def stL (e p : ℕ) := RecoveryFocus.machine (slL e p) (RowsInit.liveChain a)
def stA (e p : ℕ) := RecoveryFocus.machine (slA e p) RowsInit.hdrMachine
def stF (h15 : UnaryStage a (b15 a)) (p : ℕ) :=
  RecoveryFocus.machine (slF h15.extra p) (MaskedReset.machine h15.machine (fun _ => true))
def stP (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) := RecoveryFocus.machine (slP h15.extra P.extra) P.machine
def stR (e p : ℕ) := RecoveryFocus.machine (slR e p) (RecoveryScratchErase.resetMachine 430)

/-- **The Header writer**: ONE fixed machine (chosen from `a`, `h15`, `P` only). -/
def machine (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (stU h15.extra P.extra) (stL a h15.extra P.extra)) (stA h15.extra P.extra)) (stF a h15 P.extra))
    (stP selector a h15 P)) (stR h15.extra P.extra)

/-- The exact stage sum. -/
def costOf (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) : ℕ :=
  ((((((2 * (2 * (RowsInit.metaWord layout.w layout.degree layout.C caps.headerFuel caps.copyCap
    caps.descriptorReserve caps.rawReserve).length + 1) + 2) + 1 + RowsInit.liveCost a r) + 1 +
    RowsInit.hdrCost (Packets.pool a (r.family a) (geometryOf selector a r)) layout.w) + 1 + (2 * h15.cost r + 2)) + 1 +
    P.cost r layout.w layout.degree layout.C caps) + 1 + (2 * (2 * caps.headerFuel) + 4))

/-! ## 3. The run -/

set_option maxHeartbeats 400000 in
/-- **The Header writer's run**, for every request, layout and caps (the cost bound is `RowsHeaderWSpecOf`'s). -/
theorem run (h15 : UnaryStage a (b15 a)) (P : H282Spec selector a) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) :
    ∃ A' : Fin (440 + 4 + needH h15.extra P.extra) → List Bool,
      Step (machine selector a h15 P) (costOf selector a h15 P r layout caps) (fun _ => 0)
        (RowsInit.Hdr.hdrIn selector a (needH h15.extra P.extra) r layout caps)
        (RowsInit.Hdr.hdrOutH (needH h15.extra P.extra)) A' ∧
      (∀ k : Fin 440, A' ⟨k.val, by omega⟩ = ZeroPadding.pad (RowsConstruction.PartsStep.reserveOf caps k)
        (PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) (geometryOf selector a r) layout k)) ∧
      A' ⟨440, by omega⟩ = frame (r.input a) ∧
      A' ⟨441, by omega⟩ = rowMetadataWord layout.w layout.degree layout.C caps ∧
      A' ⟨442, by omega⟩ = List.replicate (2 * caps.headerFuel) true ∧
      A' ⟨443, by omega⟩ = List.replicate (2 * caps.headerFuel + 1) false := by
  classical
  have hm := unwrap_meta layout.w layout.degree layout.C caps
  set m := RowsInit.metaWord layout.w layout.degree layout.C caps.headerFuel caps.copyCap caps.descriptorReserve
    caps.rawReserve with hmdef
  set gs := Packets.pool a (r.family a) (geometryOf selector a r) with hgs
  set A0 := RowsInit.Hdr.hdrIn selector a (needH h15.extra P.extra) r layout caps with hA0
  have a0b : ∀ x, Fresh x.val → A0 x = [] := fun x hx => hdrIn_blank selector a _ r layout caps x hx
  -- 1. unwrap
  obtain ⟨BU, rU, bU0, bU1⟩ := unwrap_run m
  have dU := RowsInit.VecDock.run_dock rU (slU h15.extra P.extra) (slU_inj _ _) (fun _ => 0) A0 (fun _ => rfl) (by
    intro j
    fin_cases j
    · exact hm
    · rfl
    · rfl)
  set A1 := install (slU h15.extra P.extra) A0 BU with hA1
  have o1 : ∀ x, ¬ RU x.val → A1 x = A0 x := fun x hx =>
    install_other _ _ _ _ (not_hit _ _ (slU_range _ _) x hx)
  have o1v : ∀ v (hv : v < 440 + 4 + needH h15.extra P.extra), ¬ RU v → A1 ⟨v, hv⟩ = A0 ⟨v, hv⟩ :=
    fun v hv h => o1 ⟨v, hv⟩ h
  have a1_441 : A1 ⟨441, by unfold needH; omega⟩ = frame m :=
    (install_slot _ (slU_inj _ _) _ _ 0).trans bU0
  have a1_444 : A1 ⟨444, by unfold needH; omega⟩ = m :=
    (install_slot _ (slU_inj _ _) _ _ 1).trans bU1
  -- 2. the live words
  obtain ⟨AL, rL, aL0, aL62, -, aL68, aL71⟩ := RowsInit.live_chain a r
  have dL := rL.dock (slL h15.extra P.extra) (slL_inj _ _) (fun _ => 0) A1 (fun _ => rfl) (by
    intro j
    by_cases hj : j.val = 0
    · have hj0 : j = 0 := Fin.ext hj
      subst hj0
      exact (o1v 440 (by unfold needH; omega) (by unfold RU; omega)).trans (by rfl)
    · have hv : (slL h15.extra P.extra j).val = lMap j.val := rfl
      have hr := lMap_nz j.val j.isLt hj
      have hne : j ≠ 0 := fun h => hj (congrArg Fin.val h)
      rw [o1 _ (by unfold RU; omega), a0b _ (by unfold Fresh; omega)]
      simp only [RowsInit.liveIn, if_neg hne])
  set H2 := dockH (slL h15.extra P.extra) (fun _ => 0) RowsInit.liveH with hH2def
  have hH2 : ∀ x, H2 x = if x.val = 277 then 1 else 0 := by
    intro x
    by_cases hx : ∃ j, slL h15.extra P.extra j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [hH2def, dockH_slot _ (slL_inj _ _)]
      have hv : (slL h15.extra P.extra j).val = lMap j.val := rfl
      have he := lMap_277 j.val j.isLt
      by_cases hj : j.val = 71
      · have hj' : j = 71 := Fin.ext hj
        rw [if_pos (by omega)]
        subst hj'
        rfl
      · rw [if_neg (by omega)]
        have hne : j ≠ 71 := fun h => hj (congrArg Fin.val h)
        simp only [RowsInit.liveH, if_neg hne]
    · have hn : ∀ j, slL h15.extra P.extra j ≠ x := fun j h => hx ⟨j, h⟩
      rw [hH2def, dockH_other _ _ _ _ hn]
      have h277 : x.val ≠ 277 := by
        intro h
        exact hn 71 (Fin.ext (by rw [h]; rfl))
      rw [if_neg h277]
  have H2z : ∀ x, x.val ≠ 277 → H2 x = 0 := fun x hx => by rw [hH2, if_neg hx]
  set A2 := install (slL h15.extra P.extra) A1 AL with hA2
  have o2 : ∀ x, ¬ RL x.val → A2 x = A1 x := fun x hx =>
    install_other _ _ _ _ (not_hit _ _ (slL_range _ _) x hx)
  have o2v : ∀ v (hv : v < 440 + 4 + needH h15.extra P.extra), ¬ RL v → A2 ⟨v, hv⟩ = A1 ⟨v, hv⟩ :=
    fun v hv h => o2 ⟨v, hv⟩ h
  have a2_440 : A2 ⟨440, by unfold needH; omega⟩ = frame (r.input a) :=
    (install_slot _ (slL_inj _ _) _ _ 0).trans aL0
  have a2_3 : A2 ⟨3, by unfold needH; omega⟩ = UnaryTemplate.tape (RowsInit.complCount a r) :=
    (install_slot _ (slL_inj _ _) _ _ 62).trans aL62
  have a2_283 : A2 ⟨283, by unfold needH; omega⟩ = UnaryTemplate.tape (liveCount a r + 1) :=
    (install_slot _ (slL_inj _ _) _ _ 68).trans aL68
  have a2_277 : A2 ⟨277, by unfold needH; omega⟩ =
      NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word (twoK a r) :=
    (install_slot _ (slL_inj _ _) _ _ 71).trans aL71
  -- 3. the pool words and `1^w`
  have hkar : (Packets.residual (r.family a) + 1) / 2 + Packets.residual (r.family a) / 2 = RowsInit.complCount a r :=
    (geometryOf selector a r).arity
  obtain ⟨BA, dA, bA0, bA1, bA2, bA12, bA16, bA26⟩ := RowsInit.hdr_dock (slA h15.extra P.extra) (slA_inj _ _) gs
    layout.w layout.degree layout.C caps.headerFuel caps.copyCap caps.descriptorReserve caps.rawReserve H2 A2
    (fun i => by
      have hv : (slA h15.extra P.extra i).val = aMap i.val := rfl
      have hr := aMap_range i.val i.isLt
      unfold RA at hr
      exact H2z _ (by omega))
    ((o2v 0 (by unfold needH; omega) (by unfold RL; omega)).trans (o1v 0 (by unfold needH; omega) (by unfold RU; omega)))
    (a2_3.trans (congrArg UnaryTemplate.tape hkar.symm))
    ((o2v 444 (by unfold needH; omega) (by unfold RL; omega)).trans a1_444)
    (fun i hi => by
      have hv : (slA h15.extra P.extra i).val = aMap i.val := rfl
      have hr := aMap_ge3 i.val i.isLt hi
      rw [o2 _ (by unfold RL; omega), o1 _ (by unfold RU; omega), a0b _ (by unfold Fresh; omega)])
  set A3 := install (slA h15.extra P.extra) A2 BA with hA3
  have o3 : ∀ x, ¬ RA x.val → A3 x = A2 x := fun x hx =>
    install_other _ _ _ _ (not_hit _ _ (slA_range _ _) x hx)
  have o3v : ∀ v (hv : v < 440 + 4 + needH h15.extra P.extra), ¬ RA v → A3 ⟨v, hv⟩ = A2 ⟨v, hv⟩ :=
    fun v hv h => o3 ⟨v, hv⟩ h
  have a3_0 : A3 ⟨0, by unfold needH; omega⟩ = exactListWord gs := (install_slot _ (slA_inj _ _) _ _ 0).trans bA0
  have a3_3 : A3 ⟨3, by unfold needH; omega⟩ =
      UnaryTemplate.tape ((Packets.residual (r.family a) + 1) / 2 + Packets.residual (r.family a) / 2) :=
    (install_slot _ (slA_inj _ _) _ _ 1).trans bA1
  have a3_4 : A3 ⟨4, by unfold needH; omega⟩ = UnaryTemplate.tape gs.length :=
    (install_slot _ (slA_inj _ _) _ _ 12).trans bA12
  have a3_278 : A3 ⟨278, by unfold needH; omega⟩ = List.replicate (exactListWord gs).length true :=
    (install_slot _ (slA_inj _ _) _ _ 16).trans bA16
  have a3_88 : A3 ⟨88, by unfold needH; omega⟩ = List.replicate layout.w true :=
    (install_slot _ (slA_inj _ _) _ _ 26).trans bA26
  have blank3 : ∀ x, Fresh x.val → ¬ RU x.val → ¬ RL x.val → ¬ RA x.val → A3 x = [] := fun x h0 h1 h2 h3 => by
    rw [o3 x h3, o2 x h2, o1 x h1, a0b x h0]
  -- 4. Header 15
  obtain ⟨BF, rF, bF0, bF1⟩ := RowsInit.stage_masked h15 r
  have dF := RowsInit.VecDock.run_dock rF (slF h15.extra P.extra) (slF_inj _ _) H2 A3
    (fun j => by
      have hv : (slF h15.extra P.extra j).val = fMap j.val := rfl
      have hr := fMap_range h15.extra j.val j.isLt
      unfold RF at hr
      exact H2z _ (by omega))
    (fun j => by
      by_cases hj : j.val = 0
      · obtain ⟨jv, hjv⟩ := j
        simp only at hj
        subst hj
        rw [RowsInit.VecDock.vin_zero _ _ (by omega)]
        exact (o3v 440 (by unfold needH; omega) (by unfold RA; omega)).trans a2_440
      · have hv : (slF h15.extra P.extra j).val = fMap j.val := rfl
        have hr := fMap_nz h15.extra j.val j.isLt hj
        rw [RowsInit.VecDock.vin_blank _ _ j hj]
        exact blank3 _ (by unfold Fresh; omega) (by unfold RU; omega) (by unfold RL; omega) (by unfold RA; omega))
  set A4 := install (slF h15.extra P.extra) A3 BF with hA4
  have o4 : ∀ x, ¬ RF h15.extra x.val → A4 x = A3 x := fun x hx =>
    install_other _ _ _ _ (not_hit _ _ (slF_range _ _) x hx)
  have o4v : ∀ v (hv : v < 440 + 4 + needH h15.extra P.extra), ¬ RF h15.extra v → A4 ⟨v, hv⟩ = A3 ⟨v, hv⟩ :=
    fun v hv h => o4 ⟨v, hv⟩ h
  have a4_440 : A4 ⟨440, by unfold needH; omega⟩ = frame (r.input a) :=
    (install_slot _ (slF_inj _ _) _ _ ⟨0, by omega⟩).trans bF0
  have a4_15 : A4 ⟨15, by unfold needH; omega⟩ = List.replicate (b15 a r) true :=
    (install_slot _ (slF_inj _ _) _ _ ⟨1, by omega⟩).trans bF1
  -- 5. Header 282
  obtain ⟨BP, rP, bP0, bP1, bP2, bP3⟩ := P.run r layout.w layout.degree layout.C caps
  have dP := RowsInit.VecDock.run_dock rP (slP h15.extra P.extra) (slP_inj _ _) H2 A4
    (fun j => by
      have hv : (slP h15.extra P.extra j).val = pMap h15.extra j.val := rfl
      have hr := pMap_range h15.extra P.extra j.val j.isLt
      unfold RP at hr
      exact H2z _ (by omega))
    (fun j => by
      by_cases hj0 : j.val = 0
      · obtain ⟨jv, hjv⟩ := j
        simp only at hj0
        subst hj0
        exact a4_440
      · by_cases hj1 : j.val = 1
        · obtain ⟨jv, hjv⟩ := j
          simp only at hj1
          subst hj1
          exact ((o4v 441 (by unfold needH; omega) (by unfold RF; omega)).trans
            ((o3v 441 (by unfold needH; omega) (by unfold RA; omega)).trans
            ((o2v 441 (by unfold needH; omega) (by unfold RL; omega)).trans a1_441))).trans hm.symm
        · by_cases hj2 : j.val = 2
          · obtain ⟨jv, hjv⟩ := j
            simp only at hj2
            subst hj2
            exact (o4v 4 (by unfold needH; omega) (by unfold RF; omega)).trans a3_4
          · have hv : (slP h15.extra P.extra j).val = pMap h15.extra j.val := rfl
            have hr := pMap_ge3 h15.extra P.extra j.val j.isLt (by omega)
            have hin : h282In P.extra (frame (r.input a)) (rowMetadataWord layout.w layout.degree layout.C caps)
                (UnaryTemplate.tape (poolN selector a r)) j = [] := by
              unfold h282In
              rw [if_neg hj0, if_neg hj1, if_neg hj2]
            rw [hin, o4 _ (by unfold RF; omega)]
            exact blank3 _ (by unfold Fresh; omega) (by unfold RU; omega) (by unfold RL; omega) (by unfold RA; omega))
  set A5 := install (slP h15.extra P.extra) A4 BP with hA5
  have o5 : ∀ x, ¬ RP h15.extra P.extra x.val → A5 x = A4 x := fun x hx =>
    install_other _ _ _ _ (not_hit _ _ (slP_range _ _) x hx)
  have o5v : ∀ v (hv : v < 440 + 4 + needH h15.extra P.extra), ¬ RP h15.extra P.extra v →
      A5 ⟨v, hv⟩ = A4 ⟨v, hv⟩ :=
    fun v hv h => o5 ⟨v, hv⟩ h
  have a5_440 : A5 ⟨440, by unfold needH; omega⟩ = frame (r.input a) :=
    (install_slot _ (slP_inj _ _) _ _ ⟨0, by omega⟩).trans bP0
  have a5_441 : A5 ⟨441, by unfold needH; omega⟩ = rowMetadataWord layout.w layout.degree layout.C caps :=
    (install_slot _ (slP_inj _ _) _ _ ⟨1, by omega⟩).trans bP1
  have a5_4 : A5 ⟨4, by unfold needH; omega⟩ = UnaryTemplate.tape (poolN selector a r) :=
    (install_slot _ (slP_inj _ _) _ _ ⟨2, by omega⟩).trans bP2
  have a5_282 : A5 ⟨282, by unfold needH; omega⟩ =
      UnaryTemplate.tape (min layout.degree (poolN selector a r)) :=
    (install_slot _ (slP_inj _ _) _ _ ⟨3, by omega⟩).trans bP3
  have blank5 : ∀ x, Fresh x.val → ¬ RU x.val → ¬ RL x.val → ¬ RA x.val → ¬ RF h15.extra x.val →
      ¬ RP h15.extra P.extra x.val → A5 x = [] := fun x h0 h1 h2 h3 h4 h5 => by
    rw [o5 x h5, o4 x h4]
    exact blank3 x h0 h1 h2 h3
  have a5_442 : A5 ⟨442, by unfold needH; omega⟩ = List.replicate (2 * caps.headerFuel) true :=
    (o5v 442 (by unfold needH; omega) (by unfold RP; omega)).trans
    ((o4v 442 (by unfold needH; omega) (by unfold RF; omega)).trans
    ((o3v 442 (by unfold needH; omega) (by unfold RA; omega)).trans
    ((o2v 442 (by unfold needH; omega) (by unfold RL; omega)).trans
    ((o1v 442 (by unfold needH; omega) (by unfold RU; omega)).trans rfl))))
  have a5_443 : A5 ⟨443, by unfold needH; omega⟩ = List.replicate (2 * caps.headerFuel + 1) false :=
    (o5v 443 (by unfold needH; omega) (by unfold RP; omega)).trans
    ((o4v 443 (by unfold needH; omega) (by unfold RF; omega)).trans
    ((o3v 443 (by unfold needH; omega) (by unfold RA; omega)).trans
    ((o2v 443 (by unfold needH; omega) (by unfold RL; omega)).trans
    ((o1v 443 (by unfold needH; omega) (by unfold RU; omega)).trans rfl))))
  -- 6. the reserves
  have mut_val : ∀ i : Fin 430, (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val < 440 ∧
      (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 0 ∧ (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 3 ∧
      (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 4 ∧ (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 15 ∧
      (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 88 ∧ (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 262 ∧
      (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 277 ∧ (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 278 ∧
      (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 282 ∧ (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ 283 := by
    intro i
    have h := PCJ45bee56da9f34d5a_HeaderErase.mutable_not_retained i
    unfold PCJ45bee56da9f34d5a_HeaderErase.retained at h
    have := (PCJ45bee56da9f34d5a_HeaderErase.mutable i).isLt
    omega
  have dR := RowsInit.reserves_step (hdrP h15.extra P.extra) ⟨442, by unfold needH; omega⟩
    ⟨443, by unfold needH; omega⟩ (slR_inj _ _) (2 * caps.headerFuel) H2 A5
    (fun i => by
      rcases slR_val h15.extra P.extra i with ⟨j, hj⟩ | h | h
      · have := mut_val j
        exact H2z _ (by change (slR h15.extra P.extra i).val ≠ 277; omega)
      · exact H2z _ (by change (slR h15.extra P.extra i).val ≠ 277; omega)
      · exact H2z _ (by change (slR h15.extra P.extra i).val ≠ 277; omega))
    (fun i => by
      have hv : (hdrP h15.extra P.extra (PCJ45bee56da9f34d5a_HeaderErase.mutable i)).val =
        (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val := rfl
      have := mut_val i
      exact blank5 _ (by unfold Fresh; omega) (by unfold RU; omega) (by unfold RL; omega) (by unfold RA; omega)
        (by unfold RF; omega) (by unfold RP; omega))
    a5_442 a5_443
  set A6 := install (fun i => hdrP h15.extra P.extra (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) A5
    (fun _ => ZeroPadding.pad (2 * caps.headerFuel) []) with hA6
  have o6v : ∀ v (hv : v < 440 + 4 + needH h15.extra P.extra),
      (∀ i : Fin 430, (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ v) → A6 ⟨v, hv⟩ = A5 ⟨v, hv⟩ :=
    fun v hv hx => install_other _ _ _ _ (fun i h => hx i (congrArg Fin.val h))
  have hout : H2 = RowsInit.Hdr.hdrOutH (needH h15.extra P.extra) := by
    funext x
    rw [hH2]
    rfl
  have hmutinj : Function.Injective (fun i => hdrP h15.extra P.extra (PCJ45bee56da9f34d5a_HeaderErase.mutable i)) :=
    fun i j h => PCJ45bee56da9f34d5a_HeaderErase.mutable_injective (hdrP_inj _ _ h)
  -- the consumer's words
  have cw := RowsInit.common_words a (r.family a) (geometryOf selector a r) layout
  have cl := RowsInit.common_live_req a r (geometryOf selector a r) layout
  have cr := RowsInit.common_radix_req a r (geometryOf selector a r) layout
  have c262 := common_262 selector a r layout
  have ne_mut : ∀ c : ℕ, (c = 0 ∨ c = 3 ∨ c = 4 ∨ c = 15 ∨ c = 88 ∨ c = 262 ∨ c = 277 ∨ c = 278 ∨ c = 282 ∨
      c = 283 ∨ 440 ≤ c) → ∀ i : Fin 430, (PCJ45bee56da9f34d5a_HeaderErase.mutable i).val ≠ c := by
    intro c hc i
    have := mut_val i
    omega
  refine ⟨A6, (((((dU.seq dL).seq dA).seq dF).seq dP).seq dR).congr hout rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : PCJ45bee56da9f34d5a_HeaderErase.retained k
    · rw [RowsConstruction.PartsStep.reserveOf_retained caps k hk, ZeroPadding.pad_zero]
      have hkv := hk
      unfold PCJ45bee56da9f34d5a_HeaderErase.retained at hkv
      refine (o6v k.val (by unfold needH; omega) (ne_mut k.val (by omega))).trans ?_
      obtain ⟨kv, hkl⟩ := k
      simp only at hkv
      rcases hkv with h | h | h | h | h | h | h | h | h | h <;> subst h
      · exact (o5v 0 (by unfold needH; omega) (by unfold RP; omega)).trans
          ((o4v 0 (by unfold needH; omega) (by unfold RF; omega)).trans (a3_0.trans cw.1.symm))
      · exact (o5v 3 (by unfold needH; omega) (by unfold RP; omega)).trans
          ((o4v 3 (by unfold needH; omega) (by unfold RF; omega)).trans
          (a3_3.trans ((congrArg UnaryTemplate.tape hkar).trans cl.1.symm)))
      · exact a5_4.trans cw.2.2.1.symm
      · exact (o5v 15 (by unfold needH; omega) (by unfold RP; omega)).trans (a4_15.trans cr.1.symm)
      · exact (o5v 88 (by unfold needH; omega) (by unfold RP; omega)).trans
          ((o4v 88 (by unfold needH; omega) (by unfold RF; omega)).trans (a3_88.trans cw.2.2.2.symm))
      · exact (o5v 262 (by unfold needH; omega) (by unfold RP; omega)).trans
          ((o4v 262 (by unfold needH; omega) (by unfold RF; omega)).trans
          ((o3v 262 (by unfold needH; omega) (by unfold RA; omega)).trans
          ((o2v 262 (by unfold needH; omega) (by unfold RL; omega)).trans
          ((o1v 262 (by unfold needH; omega) (by unfold RU; omega)).trans (Eq.trans rfl c262.symm)))))
      · exact (o5v 277 (by unfold needH; omega) (by unfold RP; omega)).trans
          ((o4v 277 (by unfold needH; omega) (by unfold RF; omega)).trans
          ((o3v 277 (by unfold needH; omega) (by unfold RA; omega)).trans (a2_277.trans cl.2.2.symm)))
      · exact (o5v 278 (by unfold needH; omega) (by unfold RP; omega)).trans
          ((o4v 278 (by unfold needH; omega) (by unfold RF; omega)).trans (a3_278.trans cw.2.1.symm))
      · exact a5_282.trans cr.2.symm
      · exact (o5v 283 (by unfold needH; omega) (by unfold RP; omega)).trans
          ((o4v 283 (by unfold needH; omega) (by unfold RF; omega)).trans
          ((o3v 283 (by unfold needH; omega) (by unfold RA; omega)).trans (a2_283.trans cl.2.1.symm)))
    · obtain ⟨i, rfl⟩ := PCJ45bee56da9f34d5a_HeaderErase.mutable_covers k hk
      rw [RowsConstruction.PartsStep.reserveOf_mutable, PCJ45bee56da9f34d5a_HeaderErase.commonHeader_mutable]
      exact install_slot _ hmutinj _ _ i
  · exact (o6v 440 (by unfold needH; omega) (ne_mut 440 (by omega))).trans a5_440
  · exact (o6v 441 (by unfold needH; omega) (ne_mut 441 (by omega))).trans a5_441
  · exact (o6v 442 (by unfold needH; omega) (ne_mut 442 (by omega))).trans a5_442
  · exact (o6v 443 (by unfold needH; omega) (ne_mut 443 (by omega))).trans a5_443

end
end RowsHeaderW
