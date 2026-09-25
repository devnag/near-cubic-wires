import Proof.SourceAssembly.SourceInitMasters

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitE
noncomputable section

/-- The rewind block `278..283`. -/
def m278 {T : Nat} : Fin T → Bool := fun x => decide (278 ≤ x.val ∧ x.val < 284)

theorem m278_iff {T : Nat} (x : Fin T) : m278 x = true ↔ (278 ≤ x.val ∧ x.val < 284) := by
  simp [m278]

theorem m278_false {T : Nat} (x : Fin T) (h : x.val < 278 ∨ 284 ≤ x.val) : m278 x = false := by
  simp only [m278, decide_eq_false_iff_not, not_and, not_lt]
  intro h1
  omega

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

/-- **The one-time init with the rewind block cleared** (ONE fixed machine per layout and constants). -/
def initMachineE (L C cVc cS cR : ℕ) :=
  Composition.machine
    (Composition.machine
      (Once.onceMachine eR eV L C cVc pl.ds pl.b0 (d.scr pl.hT 11) (d.scr pl.hT 12) pl.mask)
      (CloseoutWitness.SelectedErase.machine (m278 (T := T)) (pl.ds (Dimension.pV eR eV)) pl.b0))
    (RecoveryFocus.machine pl.s2 (InitPost.machine L cS cR))

def initCostE (_pl : Place d eX pX gW eR eV X T) (L C cVc cS cR q b : ℕ) : ℕ :=
  (Once.onceCost eR eV L C cVc q + 1 + (2 * (cVc * RuntimeShape.tableClass L eV q) + 4)) + 1 +
    InitPost.cost L cS cR q b (cVc * RuntimeShape.tableClass L eV q) (Once.Rc eR L C q)

/-- The init with the transfer appended (SI's `init2Machine` over `initMachineE`). -/
def init2MachineE (L C cVc cS cR : ℕ) := Composition.machine (initMachineE pl L C cVc cS cR) pl.xferMachine

def init2CostE (L C cVc cS cR q b : ℕ) : ℕ :=
  initCostE pl L C cVc cS cR q b + 1 + xferCost (Once.Rc eR L C q)

/-- `s2`'s slots `6..11` are the rewind block. -/
theorem s2_rew (j : Fin 323) (h1 : 6 ≤ j.val) (h2 : j.val < 12) : (pl.s2 j).val = 272 + j.val := by
  rw [pl.s2_val]
  exact s2V_rew d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val j.val h1 h2

/-- Every other `s2` slot is off the rewind block. -/
theorem s2_off (j : Fin 323) (hj : ¬ (6 ≤ j.val ∧ j.val < 12)) :
    (pl.s2 j).val < 278 ∨ 284 ≤ (pl.s2 j).val := by
  by_contra hc
  have hc1 : 278 ≤ (pl.s2 j).val := by omega
  have hc2 : (pl.s2 j).val < 284 := by omega
  have hlt : (pl.s2 j).val - 272 < 323 := by omega
  have e : pl.s2 ⟨(pl.s2 j).val - 272, hlt⟩ = pl.s2 j := by
    apply Fin.ext
    rw [s2_rew pl ⟨(pl.s2 j).val - 272, hlt⟩ (by show 6 ≤ (pl.s2 j).val - 272; omega)
      (by show (pl.s2 j).val - 272 < 12; omega)]
    show 272 + ((pl.s2 j).val - 272) = (pl.s2 j).val
    omega
  have hjj := pl.s2_inj e
  apply hj
  rw [← hjj]
  exact ⟨by show 6 ≤ (pl.s2 j).val - 272; omega, by show (pl.s2 j).val - 272 < 12; omega⟩

/-- Every tape of the rewind block is an `s2` slot. -/
theorem rew_in_s2 (x : Fin T) (h1 : 278 ≤ x.val) (h2 : x.val < 284) : ∃ j, pl.s2 j = x := by
  have hlt : x.val - 272 < 323 := by omega
  refine ⟨⟨x.val - 272, hlt⟩, Fin.ext ?_⟩
  rw [s2_rew pl ⟨x.val - 272, hlt⟩ (by show 6 ≤ x.val - 272; omega) (by show x.val - 272 < 12; omega)]
  show 272 + (x.val - 272) = x.val
  omega

/-- **THE INIT WITH THE REWIND BLOCK CLEARED, run.** SI's `init_run` with `hlow` (blank rewind block) replaced by `hlowE` (every tape of
`278..283` of length `≤ Vv`, head `0`), and `Vv + 1 ≤ Rc`. Same exit `InitOut`. -/
theorem init_runE (L C cVc cS cR q b : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hAr : A pl.ar = UnaryTemplate.tape q) (hHr : H pl.ar = 0)
    (hAw : A pl.wd = List.replicate b true) (hHw : H pl.wd = 0)
    (hlowE : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 →
      (A x).length ≤ cVc * RuntimeShape.tableClass L eV q ∧ H x = 0)
    (hF : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A x = [] ∧ H x = 0)
    (hfit : q + 3 + Dimension.prefixCost eR eV L C cVc q ≤ Once.Rc eR L C q)
    (hVR : cVc * RuntimeShape.tableClass L eV q ≤ Once.Rc eR L C q)
    (hV1 : cVc * RuntimeShape.tableClass L eV q + 1 ≤ Once.Rc eR L C q)
    (hVLR : VLog eV L cVc q ≤ Once.Rc eR L C q) (hRc : 2 ≤ Once.Rc eR L C q) :
    ∃ A' : Fin T → List Bool,
      Step (initMachineE pl L C cVc cS cR) (initCostE pl L C cVc cS cR q b) H A
        (dockH pl.s2 H InitPost.outH) A' ∧
      InitOut pl L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) H A
        (dockH pl.s2 H InitPost.outH) A' := by
  obtain ⟨hF', hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hX := pl.ext.hX
  have ha := pl.har
  have hw := pl.hwd
  -- `Once`'s entry (as SI's `init_run`)
  have hdsF : ∀ x : Fin (Dimension.P eR eV), x.val ≠ 0 → d.F ≤ (pl.ds x).val ∧ (pl.ds x).val < d.U := by
    intro x hx; rw [pl.ds_pos x hx]; have := x.isLt; omega
  have hHds : ∀ x, H (pl.ds x) = 0 := by
    intro x
    by_cases h0 : x.val = 0
    · rw [pl.ds_zero x h0]; exact hHr
    · exact (hF _ (hdsF x h0).1 (hdsF x h0).2).2
  have hAds : ∀ x, A (pl.ds x) = Dimension.input eR eV q x := by
    intro x
    by_cases h0 : x.val = 0
    · rw [pl.ds_zero x h0, hAr]; simp [Dimension.input, h0]
    · rw [(hF _ (hdsF x h0).1 (hdsF x h0).2).1]; simp [Dimension.input, h0]
  have hb0v : pl.b0.val = JB d eX pX gW + Dimension.P eR eV := rfl
  have hb0 : d.F ≤ pl.b0.val ∧ pl.b0.val < d.U := by rw [hb0v]; omega
  have hs11 : d.F ≤ (d.scr pl.hT 11).val ∧ (d.scr pl.hT 11).val < d.U := by
    show d.F ≤ d.scrV 11 ∧ d.scrV 11 < d.U; omega
  have hs12 : d.F ≤ (d.scr pl.hT 12).val ∧ (d.scr pl.hT 12).val < d.U := by
    show d.F ≤ d.scrV 12 ∧ d.scrV 12 < d.U; omega
  have hother : ∀ y, pl.mask y = true → (∀ x, pl.ds x ≠ y) → y ≠ pl.b0 →
      H y = 0 ∧ (A y).length ≤ Once.Rc eR L C q := by
    intro y hy _ _
    simp only [Place.mask, decide_eq_true_eq] at hy
    obtain ⟨hA, hH⟩ := hF y hy.1 hy.2.1
    exact ⟨hH, by rw [hA]; simp⟩
  obtain ⟨A1, s1, hA1d, hA1l, hA1m, hA1q, hA1Rl, hA1V, hA1Vl, hA1off⟩ :=
    Once.once_run eR eV L C cVc q pl.ds pl.ds_inj pl.b0 (d.scr pl.hT 11) (d.scr pl.hT 12)
      pl.ds_ne_b0 (pl.ds_ne_scr 11) (pl.ds_ne_scr 12) (pl.b0_ne_scr 11) (pl.b0_ne_scr 12) pl.scr_ne
      pl.mask pl.mask_pq pl.mask_pRl pl.mask_pV pl.mask_pVl pl.mask_scr11 pl.mask_scr12
      H A hHds hAds (hF _ hb0.1 hb0.2).2 (hF _ hb0.1 hb0.2).1 (hF _ hs11.1 hs11.2).2 (hF _ hs11.1 hs11.2).1
      (hF _ hs12.1 hs12.2).2 (hF _ hs12.1 hs12.2).1 hother hfit
  rw [pl.ds_zero _ rfl] at hA1q
  have hRl : Once.Rc eR L C q ≤ (A1 (pl.ds (Dimension.pRl eR eV))).length := by
    rw [hA1Rl]; exact rcLog_long eR L C q
  set Rc := Once.Rc eR L C q with hRcd
  set Vv := cVc * RuntimeShape.tableClass L eV q with hVv
  -- the rewind block: below `F`, untouched by `Once`
  have hmF : ∀ x : Fin T, m278 x = true → x.val < d.F := fun x hx => by
    have := (m278_iff x).1 hx; omega
  have hA1low : ∀ x : Fin T, m278 x = true → A1 x = A x := by
    intro x hx
    have hxF := hmF x hx
    have hxv := (m278_iff x).1 hx
    refine hA1off x (pl.mask_false_lt x hxF) ?_ ?_ ?_ ?_
    · intro y hy
      by_cases h0 : y.val = 0
      · rw [pl.ds_zero y h0] at hy
        have hv : pl.ar.val = x.val := congrArg Fin.val hy
        omega
      · have hy2 := (hdsF y h0).1
        rw [hy] at hy2
        omega
    · intro h; rw [h] at hxF; omega
    · intro h; rw [h] at hxF; omega
    · intro h; rw [h] at hxF; omega
  -- the erase: driver `ds pV = 1^Vv`, log `b0 = 0^Rc`
  have hpV0 : (Dimension.pV eR eV).val ≠ 0 := by
    have := Place.pV_val (eR := eR) (eV := eV); have := Dimension.P_ge eR eV; omega
  have hdm : m278 (pl.ds (Dimension.pV eR eV)) = false :=
    m278_false _ (Or.inr (by have := (hdsF _ hpV0).1; omega))
  have hlm : m278 pl.b0 = false := m278_false _ (Or.inr (by omega))
  have hpRl := (Dimension.pRl eR eV).isLt
  have hpRlv := Place.pRl_val (eR := eR) (eV := eV)
  have hbm : pl.mask pl.b0 = true :=
    pl.mask_true pl.b0 hb0.1 hb0.2 (by rw [hb0v]; omega) (by rw [hb0v]; omega) (by rw [hb0v]; omega)
      (by rw [hb0v]; omega) (by rw [hb0v]; omega)
  have hA1b0 : A1 pl.b0 = List.replicate Rc false := hA1m _ hbm
  have sE := BlockPlatform.Scrub.erase_step (m278 (T := T)) (pl.ds (Dimension.pV eR eV)) pl.b0 hdm hlm
    (pl.ds_ne_b0 _) Vv Rc hV1 H A1
    (by
      intro i hi
      rcases hi with hi | hi | hi
      · exact (hlowE i ((m278_iff i).1 hi).1 ((m278_iff i).1 hi).2).2
      · rw [hi]; exact hHds _
      · rw [hi]; exact (hF _ hb0.1 hb0.2).2)
    (by
      intro i hi
      rw [hA1low i hi]
      exact (hlowE i ((m278_iff i).1 hi).1 ((m278_iff i).1 hi).2).1)
    hA1V hA1b0
  -- the state SI's `InitPost` would see with a blank rewind block
  let Ahat : Fin T → List Bool := fun x => if m278 x = true then [] else A x
  let A1' : Fin T → List Bool := fun x => if m278 x = true then [] else A1 x
  have hAhat : ∀ x : Fin T, (x.val < 278 ∨ 284 ≤ x.val) → Ahat x = A x := fun x hx => by
    simp only [Ahat, m278_false x hx, Bool.false_eq_true, if_false]
  have hA1' : ∀ x : Fin T, (x.val < 278 ∨ 284 ≤ x.val) → A1' x = A1 x := fun x hx => by
    simp only [A1', m278_false x hx, Bool.false_eq_true, if_false]
  have hgeF : ∀ x : Fin T, d.F ≤ x.val → (x.val < 278 ∨ 284 ≤ x.val) := fun x hx => Or.inr (by omega)
  have hin := pl.post_input q b Vv (VLog eV L cVc q) Rc Ahat A1'
    ((hAhat _ hw.2).trans hAw)
    (fun x h1 h2 => by simp only [Ahat, (m278_iff x).2 ⟨h1, h2⟩, if_true])
    ((hA1' _ ha.2).trans hA1q)
    ((hA1' _ (hgeF _ (hdsF _ hpV0).1)).trans hA1V)
    ((hA1' _ (hgeF _ (hdsF _ (by have := Place.pVl_val (eR := eR) (eV := eV); have := Dimension.P_ge eR eV; omega)).1)).trans hA1Vl)
    ((hA1' _ (hgeF _ hs11.1)).trans hA1d)
    ((hA1' _ (hgeF _ hs12.1)).trans hA1l)
    (fun y hy => by
      have hyF : d.F ≤ y.val := by simp only [Place.mask, decide_eq_true_eq] at hy; exact hy.1
      rw [hA1' y (hgeF y hyF)]; exact hA1m y hy)
    (fun y h1 h2 h3 h4 h5 => by
      simp only [A1', Ahat]
      split_ifs with hm
      · rfl
      · exact hA1off y h1 h2 h3 h4 h5)
  -- `InitPost`, run from the zero-padded input
  obtain ⟨W, sW, hW⟩ : ∃ W, Step (InitPost.machine L cS cR)
      (InitPost.cost L cS cR q b Vv Rc) (fun _ => 0)
      (InitPost.input q b Vv (VLog eV L cVc q) Rc)
      InitPost.outH W ∧ PostOut L cS cR q b Vv Rc W :=
    InitPost.post_run L cS cR q b _ _ _ hVR hVLR (by omega)
  let capj : Fin 323 → ℕ := fun j => if 6 ≤ j.val ∧ j.val < 12 then Vv else 0
  let W' : Fin 323 → List Bool := fun j => ZeroPadding.pad (capj j) (W j)
  have hW6 := hW.2.2.2.2.1
  have hW7 := hW.2.2.2.2.2.1
  have hagreeW : ∀ j : Fin 323, (j.val < 8 ∨ 12 ≤ j.val) → W' j = W j := by
    intro j hj
    simp only [W', capj]
    by_cases h67 : 6 ≤ j.val ∧ j.val < 12
    · rw [if_pos h67]
      by_cases h6 : j.val = 6
      · have e : j = 6 := Fin.ext h6
        subst e
        rw [hW6]; simp [ZeroPadding.pad]
      · have e : j = 7 := Fin.ext (by show j.val = 7; omega)
        subst e
        rw [hW7]; simp [ZeroPadding.pad]
    · rw [if_neg h67, ZeroPadding.pad_zero]
  have hW' : PostOut L cS cR q b Vv Rc W' := by
    obtain ⟨w0, w1, w4, w5, w6, w7, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26,
      w27, w28, w29, w30, w31, w2, w3, wl⟩ := hW
    exact ⟨(hagreeW 0 (Or.inl (by decide))).trans w0, (hagreeW 1 (Or.inl (by decide))).trans w1,
      (hagreeW 4 (Or.inl (by decide))).trans w4, (hagreeW 5 (Or.inl (by decide))).trans w5,
      (hagreeW 6 (Or.inl (by decide))).trans w6, (hagreeW 7 (Or.inl (by decide))).trans w7,
      (hagreeW 12 (Or.inr (by decide))).trans w12, (hagreeW 13 (Or.inr (by decide))).trans w13,
      (hagreeW 14 (Or.inr (by decide))).trans w14, (hagreeW 15 (Or.inr (by decide))).trans w15,
      (hagreeW 16 (Or.inr (by decide))).trans w16, (hagreeW 17 (Or.inr (by decide))).trans w17,
      (hagreeW 18 (Or.inr (by decide))).trans w18, (hagreeW 19 (Or.inr (by decide))).trans w19,
      (hagreeW 20 (Or.inr (by decide))).trans w20, (hagreeW 21 (Or.inr (by decide))).trans w21,
      (hagreeW 22 (Or.inr (by decide))).trans w22, (hagreeW 23 (Or.inr (by decide))).trans w23,
      (hagreeW 24 (Or.inr (by decide))).trans w24, (hagreeW 25 (Or.inr (by decide))).trans w25,
      (hagreeW 26 (Or.inr (by decide))).trans w26, (hagreeW 27 (Or.inr (by decide))).trans w27,
      (hagreeW 28 (Or.inr (by decide))).trans w28, (hagreeW 29 (Or.inr (by decide))).trans w29,
      (hagreeW 30 (Or.inr (by decide))).trans w30, (hagreeW 31 (Or.inr (by decide))).trans w31,
      (hagreeW 2 (Or.inl (by decide))).trans w2, (hagreeW 3 (Or.inl (by decide))).trans w3,
      fun i hi => by rw [hagreeW i (Or.inr hi)]; exact wl i hi⟩
  set A2 := BlockPlatform.Scrub.blank (m278 (T := T)) A1 Vv with hA2
  have hA2in : ∀ j, A2 (pl.s2 j) = ZeroPadding.pad (capj j) (InitPost.input q b Vv (VLog eV L cVc q) Rc j) := by
    intro j
    rw [← hin j]
    by_cases h : 6 ≤ j.val ∧ j.val < 12
    · have hv := s2_rew pl j h.1 h.2
      have hm : m278 (pl.s2 j) = true := (m278_iff _).2 ⟨by omega, by omega⟩
      simp only [A2, BlockPlatform.Scrub.blank, A1', capj, hm, if_true, if_pos h]
      simp [ZeroPadding.pad]
    · have hm : m278 (pl.s2 j) = false := m278_false _ (s2_off pl j h)
      simp only [A2, BlockPlatform.Scrub.blank, A1', capj, hm, Bool.false_eq_true, if_false, if_neg h,
        ZeroPadding.pad_zero]
  have hHs2 : ∀ j, H (pl.s2 j) = 0 := by
    intro j
    by_cases h : 6 ≤ j.val ∧ j.val < 12
    · have hv := s2_rew pl j h.1 h.2
      exact (hlowE _ (by omega) (by omega)).2
    · have hin2 := s2V_in d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val j.val j.isLt
      rw [← Place.s2_val] at hin2
      have hoff := s2_off pl j h
      unfold InS2 at hin2
      rcases hin2 with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
      · rw [Fin.ext h']; exact hHr
      · rw [Fin.ext h']; exact hHw
      · exact (hF _ (by omega) (by omega)).2
      · exact (hF _ (by omega) (by omega)).2
      · exact (hF _ (by omega) (by omega)).2
      · exact (hF _ (by omega) (by omega)).2
      · exact absurd h'.2 (by omega)
      · exact (hF _ (by omega) (by omega)).2
      · exact (hF _ (by omega) (by omega)).2
      · exact (hF _ (by omega) (by omega)).2
      · exact (hF _ (by omega) (by omega)).2
  have s2step := (sW.pad capj).dock pl.s2 pl.s2_inj H A2 hHs2 hA2in
  have hinst : install pl.s2 A2 W' = install pl.s2 A1' W' := by
    funext x
    by_cases hx : ∃ j, pl.s2 j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [install_slot _ pl.s2_inj, install_slot _ pl.s2_inj]
    · have hx' : ∀ j, pl.s2 j ≠ x := fun j h => hx ⟨j, h⟩
      rw [install_other _ A2 W' x hx', install_other _ A1' W' x hx']
      have hoff : x.val < 278 ∨ 284 ≤ x.val := by
        by_contra hc
        exact hx (rew_in_s2 pl x (by omega) (by omega))
      have hm : m278 x = false := m278_false x hoff
      simp only [A2, BlockPlatform.Scrub.blank, A1', hm, Bool.false_eq_true, if_false]
  rw [hinst] at s2step
  -- the exit, by SI's own lemmas at `(Ahat, A1', W')`
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14⟩ :=
    pl.out_res L cS cR q b Rc Vv hRc H A1' W' hW'
  obtain ⟨e1, e2, e3⟩ := pl.out_enc L cS cR q b Rc Vv H A1' W' hW'
  have hAr' : Ahat pl.ar = UnaryTemplate.tape q := (hAhat _ ha.2).trans hAr
  have hAw' : Ahat pl.wd = List.replicate b true := (hAhat _ hw.2).trans hAw
  have hFh : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → Ahat x = [] ∧ H x = 0 := fun x h1 h2 => by
    rw [hAhat x (hgeF x h1)]; exact hF x h1 h2
  have hmh : ∀ y, pl.mask y = true → A1' y = List.replicate Rc false := fun y hy => by
    have hyF : d.F ≤ y.val := by simp only [Place.mask, decide_eq_true_eq] at hy; exact hy.1
    rw [hA1' y (hgeF y hyF)]; exact hA1m y hy
  have hRlh : Rc ≤ (A1' (pl.ds (Dimension.pRl eR eV))).length := by
    have hpRl0 : (Dimension.pRl eR eV).val ≠ 0 := by omega
    rw [hA1' _ (hgeF _ (hdsF _ hpRl0).1)]; exact hRl
  have hoffh : ∀ y, pl.mask y = false → (∀ x, pl.ds x ≠ y) → y ≠ pl.b0 → y ≠ d.scr pl.hT 11 →
      y ≠ d.scr pl.hT 12 → A1' y = Ahat y := fun y h1 h2 h3 h4 h5 => by
    simp only [A1', Ahat]
    split_ifs with hm
    · rfl
    · exact hA1off y h1 h2 h3 h4 h5
  obtain ⟨f1, f2, f3, f4, f5⟩ := pl.out_frame L cS cR q b Rc Vv H Ahat A1' W' hW' hAr' hHr hAw' hHw hFh hmh hRlh hoffh
  have f3' : ∀ x : Fin T, x.val < d.F → (x.val < 278 ∨ 284 ≤ x.val) →
      install pl.s2 A1' W' x = A x ∧ dockH pl.s2 H InitPost.outH x = H x := fun x h1 h2 => by
    rw [← hAhat x h2]; exact f3 x h1 h2
  have f5' : ∀ x : Fin T, d.U ≤ x.val →
      install pl.s2 A1' W' x = A x ∧ dockH pl.s2 H InitPost.outH x = H x := fun x h1 => by
    rw [← hAhat x (Or.inr (by omega))]; exact f5 x h1
  exact ⟨_, (s1.seq sE).seq s2step,
    ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14,
      fun en old => (e1 en old).1, fun en old => (e1 en old).2.1, fun en old => (e1 en old).2.2.1,
      fun en old => (e1 en old).2.2.2.1, fun en old => (e1 en old).2.2.2.2,
      fun en xs => (e2 en xs).1, fun en xs => (e2 en xs).2.1, fun en xs => (e2 en xs).2.2,
      e3, f1, f2, f3', f4, f5'⟩⟩

/-- **THE INIT WITH THE REWIND BLOCK CLEARED, then the transfer** (SI's `init2_run` over `init_runE`): same exit `InitOutM`. -/
theorem init2_runE (L C cVc cS cR q b : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hAr : A pl.ar = UnaryTemplate.tape q) (hHr : H pl.ar = 0)
    (hAw : A pl.wd = List.replicate b true) (hHw : H pl.wd = 0)
    (hlowE : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 →
      (A x).length ≤ cVc * RuntimeShape.tableClass L eV q ∧ H x = 0)
    (hF : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A x = [] ∧ H x = 0)
    (hfit : q + 3 + Dimension.prefixCost eR eV L C cVc q ≤ Once.Rc eR L C q)
    (hVR : cVc * RuntimeShape.tableClass L eV q ≤ Once.Rc eR L C q)
    (hVLR : VLog eV L cVc q ≤ Once.Rc eR L C q) (hRc : 2 ≤ Once.Rc eR L C q)
    (hU0 : U0 L q ≤ Once.Rc eR L C q)
    (hS : cS * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hR : cR * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hB : cVc * RuntimeShape.tableClass L eV q + 1 + 2 ≤ Once.Rc eR L C q)
    (hv : b + 2 ≤ Once.Rc eR L C q) :
    ∃ (H' : Fin T → ℕ) (A' : Fin T → List Bool),
      Step (init2MachineE pl L C cVc cS cR) (init2CostE pl L C cVc cS cR q b) H A H' A' ∧
      InitOutM pl L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) H A H' A' := by
  obtain ⟨A1, s1, ho⟩ := init_runE pl L C cVc cS cR q b H A hAr hHr hAw hHw hlowE hF hfit hVR (by omega) hVLR hRc
  set Rc := Once.Rc eR L C q with hRcd
  set Vv := cVc * RuntimeShape.tableClass L eV q with hVv
  set H1 := dockH pl.s2 H InitPost.outH with hH1
  obtain ⟨hF', hB', h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have e0 : Dims.rfT pl.ext2 pl.hT 0 = Dims.csSlots pl.ext.rest.ext pl.hT 2 := Fin.ext rfl
  have e1 : Dims.rfT pl.ext2 pl.hT 1 = Dims.drvSlots pl.ext.rest.ext pl.hT 0 := Fin.ext rfl
  have e2 : Dims.rfT pl.ext2 pl.hT 2 = Dims.drvSlots pl.ext.rest.ext pl.hT 1 := Fin.ext rfl
  have e3 : Dims.rfT pl.ext2 pl.hT 3 = Dims.drvSlots pl.ext.rest.ext pl.hT 2 := Fin.ext rfl
  have e4 : Dims.rfT pl.ext2 pl.hT 4 = Dims.drvSlots pl.ext.rest.ext pl.hT 4 := Fin.ext rfl
  have ht : ∀ i, A1 (Dims.rfT pl.ext2 pl.hT i) = masterW L cS cR q b Rc Vv i := by
    intro i
    fin_cases i
    · show A1 (Dims.rfT pl.ext2 pl.hT 0) = masterW L cS cR q b Rc Vv 0
      rw [e0]; exact ho.u0.1
    · show A1 (Dims.rfT pl.ext2 pl.hT 1) = masterW L cS cR q b Rc Vv 1
      rw [e1]; exact ho.drvS.1
    · show A1 (Dims.rfT pl.ext2 pl.hT 2) = masterW L cS cR q b Rc Vv 2
      rw [e2]; exact ho.drvR.1
    · show A1 (Dims.rfT pl.ext2 pl.hT 3) = masterW L cS cR q b Rc Vv 3
      rw [e3]; exact ho.drvB.1
    · show A1 (Dims.rfT pl.ext2 pl.hT 4) = masterW L cS cR q b Rc Vv 4
      rw [e4]; exact ho.drvV.1
  have htH0 : H1 (Dims.rfT pl.ext2 pl.hT 0) = 0 := by rw [e0]; exact ho.u0.2
  have htH : ∀ i : Fin 5, i.val ≠ 0 → H1 (Dims.rfT pl.ext2 pl.hT i) = 1 := by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    · show H1 (Dims.rfT pl.ext2 pl.hT 1) = 1
      rw [e1]; exact ho.drvS.2
    · show H1 (Dims.rfT pl.ext2 pl.hT 2) = 1
      rw [e2]; exact ho.drvR.2
    · show H1 (Dims.rfT pl.ext2 pl.hT 3) = 1
      rw [e3]; exact ho.drvB.2
    · show H1 (Dims.rfT pl.ext2 pl.hT 4) = 1
      rw [e4]; exact ho.drvV.2
  have hmB : ∀ i, A1 (Dims.mT pl.ext2 pl.hT i) = List.replicate Rc false ∧ H1 (Dims.mT pl.ext2 pl.hT i) = 0 := by
    intro i
    have hres2 := pl.ext.hjunk
    exact ho.blank _ (by rw [pl.mT_val]; omega) (by rw [pl.mT_val]; have := i.isLt; omega)
      (by unfold Kept; rw [pl.mT_val]; have := i.isLt; omega)
  obtain ⟨A2, s2, hm2, ho2, ht2, hh2⟩ := pl.xfer_run Rc (masterW L cS cR q b Rc Vv)
    (masterW_length L cS cR q b Rc Vv hU0 hS hR hB hv) H1 A1 ht htH0 htH (fun i => (hmB i).1)
    (fun i => (hmB i).2) ho.drv.1 ho.drv.2 ho.log.1 ho.log.2
  exact ⟨_, A2, s1.seq s2, pl.outM L cS cR q b Rc Vv H A H1 A1 A2 ho hm2 ho2 ht2 hh2⟩

end
end NearCubicWires.SourceSkeleton.InitE
end

