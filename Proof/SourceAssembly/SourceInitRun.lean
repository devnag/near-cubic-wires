import Proof.SourceAssembly.SourceInitLayout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
open PCJ1fef9807c6954e94_Native
namespace NearCubicWires.SourceConstruction.InitRun
noncomputable section

/-! ## 1. The values -/

/-- The live count `K`. -/
abbrev Kc (L q : ℕ) : ℕ := normalizedLiveCount q L
/-- `U0 = 3(K+3) + 2⌈(q-K)/2⌉` (`RowConst.U0_eq`). -/
abbrev U0 (L q : ℕ) : ℕ := 3*(Kc L q+2+1) + ((q - Kc L q+1)/2 + (q - Kc L q+1)/2)
/-- The big slope `Mb = uniformDeg q L · Ms`. -/
abbrev Mb (L q : ℕ) : ℕ := q / InitSlopes.dv L q * InitPost.Ms L q
/-- The encoder's uniform `D` and `cap` (`D + 1 = cap`, `D ≥ 20b+22`). -/
abbrev D0 (b : ℕ) : ℕ := InitEnc.rr b + 1
abbrev cap0 (b : ℕ) : ℕ := InitEnc.rr b + 2
/-- `V`'s exact log from the pipeline. -/
abbrev VLog (eV L cVc q : ℕ) : ℕ := cVc*(q+1)^eV*(2*2^(q - normalizedLiveCount q L)+3)+2

def Kept (d : Dims) (eX pX gW X : Nat) (v : Nat) : Prop :=
  v = d.scrV 11 ∨ v = d.scrV 12 ∨ (d.B + 14 ≤ v ∧ v < d.B + 19) ∨
  (d.B + 19 + restPc eX pX gW ≤ v ∧ v < d.B + 24 + restPc eX pX gW) ∨ (d.F + d.rt + 3 ≤ v ∧ v < d.F + d.rt + 13) ∨
  (JB d eX pX gW ≤ v ∧ v < JB d eX pX gW + X)

/-! ## 2. The machine -/

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

def initCost (_pl : Place d eX pX gW eR eV X T) (L C cVc cS cR q b : ℕ) : ℕ :=
  Once.onceCost eR eV L C cVc q + 1 +
    InitPost.cost L cS cR q b (cVc * RuntimeShape.tableClass L eV q) (Once.Rc eR L C q)

end Place

/-! ## 3. The exit, in the consumers' terms -/

structure InitOut {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)
    (L cS cR q b Rc Vv : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool) (H' : Fin T → ℕ) (A' : Fin T → List Bool) :
    Prop where
  drv : A' (d.scr pl.hT 11) = List.replicate Rc true ∧ H' (d.scr pl.hT 11) = 0
  log : A' (d.scr pl.hT 12) = List.replicate (Rc+2) false ∧ H' (d.scr pl.hT 12) = 0
  rew1 : A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = List.replicate Vv true ∧
    H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = 0
  rew2 : A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = List.replicate Vv false ∧
    H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = 0
  u0 : A' (Dims.csSlots pl.ext.rest.ext pl.hT 2) = ZeroPadding.pad Rc (List.replicate (U0 L q) true) ∧
    H' (Dims.csSlots pl.ext.rest.ext pl.hT 2) = 0
  drvS : A' (Dims.drvSlots pl.ext.rest.ext pl.hT 0) = ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(Vv+1))) ∧
    H' (Dims.drvSlots pl.ext.rest.ext pl.hT 0) = 1
  drvR : A' (Dims.drvSlots pl.ext.rest.ext pl.hT 1) = ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(Vv+1))) ∧
    H' (Dims.drvSlots pl.ext.rest.ext pl.hT 1) = 1
  drvB : A' (Dims.drvSlots pl.ext.rest.ext pl.hT 2) = ZeroPadding.pad Rc (UnaryTemplate.tape (Vv+1)) ∧
    H' (Dims.drvSlots pl.ext.rest.ext pl.hT 2) = 1
  drvV : A' (Dims.drvSlots pl.ext.rest.ext pl.hT 4) = ZeroPadding.pad Rc (UnaryTemplate.tape b) ∧
    H' (Dims.drvSlots pl.ext.rest.ext pl.hT 4) = 1
  big : A' (Dims.rsT pl.ext.rest pl.hT 0) = ZeroPadding.pad Rc (List.replicate (Mb L q) true) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 0) = 0
  small : A' (Dims.rsT pl.ext.rest pl.hT 1) = ZeroPadding.pad Rc (List.replicate (InitPost.Ms L q) true) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 1) = 0
  curT : A' (Dims.rsT pl.ext.rest pl.hT 2) = ZeroPadding.pad Rc (UnaryTemplate.tape 0) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 2) = 0
  wres : A' (Dims.rsT pl.ext.rest pl.hT 3) = ZeroPadding.pad Rc (List.replicate b true) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 3) = 0
  qres : A' (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true) ∧
    H' (Dims.rsT pl.ext.rest pl.hT 4) = 0
  enc3 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 3) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 3) ∧
    H' (Dims.encT (d := d) pl.hT 3) = 0
  enc7 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 6) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 7) ∧
    H' (Dims.encT (d := d) pl.hT 6) = 0
  enc8 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 7) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 8) ∧
    H' (Dims.encT (d := d) pl.hT 7) = 0
  enc9 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 8) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 9) ∧
    H' (Dims.encT (d := d) pl.hT 8) = 0
  enc10 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A' (Dims.encT (d := d) pl.hT 9) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 10) ∧
    H' (Dims.encT (d := d) pl.hT 9) = 0
  app2 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A' (Dims.encT (d := d) pl.hT 10) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 2) ∧
    H' (Dims.encT (d := d) pl.hT 10) = 0
  app4 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A' (Dims.encT (d := d) pl.hT 11) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 4) ∧
    H' (Dims.encT (d := d) pl.hT 11) = 0
  app5 : ∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A' (Dims.encT (d := d) pl.hT 12) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 5) ∧
    H' (Dims.encT (d := d) pl.hT 12) = 0
  encOld : ∀ kk : Fin 13, (kk.val = 4 ∨ kk.val = 5) →
    A' (Dims.encT (d := d) pl.hT kk) = List.replicate Rc false ∧ H' (Dims.encT (d := d) pl.hT kk) = 0
  blank : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → ¬ Kept d eX pX gW X x.val →
    A' x = List.replicate Rc false ∧ H' x = 0
  junk : ∀ x : Fin T, JB d eX pX gW ≤ x.val → x.val < JB d eX pX gW + X → Rc ≤ (A' x).length ∧ H' x = 0
  below : ∀ x : Fin T, x.val < d.F → (x.val < 278 ∨ 284 ≤ x.val) → A' x = A x ∧ H' x = H x
  low : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 → H' x = 0
  above : ∀ x : Fin T, d.U ≤ x.val → A' x = A x ∧ H' x = H x

/-! ## 4. Where the residents sit in the dock -/

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

theorem at4 : d.scr pl.hT 11 = pl.s2 4 :=
  Fin.ext (s2V_4 d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val).symm
theorem at5 : d.scr pl.hT 12 = pl.s2 5 :=
  Fin.ext (s2V_5 d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val).symm
theorem at6 : Dims.rewind2Slots pl.ext.rest.ext pl.hT 1 = pl.s2 6 := Fin.ext (by
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 6
  rw [s2V_rew d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 6 (by decide) (by decide)]; rfl)
theorem at7 : Dims.rewind2Slots pl.ext.rest.ext pl.hT 2 = pl.s2 7 := Fin.ext (by
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 7
  rw [s2V_rew d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 7 (by decide) (by decide)]; rfl)
theorem at12 : Dims.csSlots pl.ext.rest.ext pl.hT 2 = pl.s2 12 := Fin.ext (by
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 12
  rw [s2V_cs d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 12 (by decide) (by decide)]; rfl)
theorem at13 : Dims.drvSlots pl.ext.rest.ext pl.hT 0 = pl.s2 13 := Fin.ext (by
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 13
  rw [s2V_cs d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 13 (by decide) (by decide)]; rfl)
theorem at14 : Dims.drvSlots pl.ext.rest.ext pl.hT 1 = pl.s2 14 := Fin.ext (by
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 14
  rw [s2V_cs d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 14 (by decide) (by decide)]; rfl)
theorem at15 : Dims.drvSlots pl.ext.rest.ext pl.hT 2 = pl.s2 15 := Fin.ext (by
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 15
  rw [s2V_cs d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 15 (by decide) (by decide)]; rfl)
theorem at16 : Dims.drvSlots pl.ext.rest.ext pl.hT 4 = pl.s2 16 := Fin.ext (by
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 16
  rw [s2V_cs d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 16 (by decide) (by decide)]; rfl)
theorem atRs (k : Fin 5) : Dims.rsT pl.ext.rest pl.hT k = pl.s2 ⟨17 + k.val, by omega⟩ := Fin.ext (by
  rw [s2_val, s2V_rs d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val (17 + k.val) (by omega) (by omega)]
  show d.B + 19 + restPc eX pX gW + k.val = _
  omega)
theorem atEnc (k : Fin 13) (h1 : 3 ≤ k.val) : Dims.encT (d := d) pl.hT k = pl.s2 ⟨k.val + 19, by omega⟩ :=
  Fin.ext (by
    rw [s2_val, s2V_enc d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val (k.val + 19) (by omega) (by omega)]
    show d.F + d.rt + k.val = _
    omega)
theorem at0 : pl.ar = pl.s2 0 := Fin.ext (by rw [s2_val]; simp [s2V])
theorem at1 : pl.wd = pl.s2 1 := Fin.ext (by rw [s2_val]; simp [s2V])

/-! ## 5. `Once`'s side conditions on this placement -/

theorem ds_ne_b0 : ∀ x, pl.ds x ≠ pl.b0 := by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have ha := pl.har.1
  intro x h
  have hv := congrArg Fin.val h
  have hx := x.isLt
  by_cases h0 : x.val = 0
  · rw [pl.ds_zero x h0] at hv; simp only [b0] at hv; omega
  · rw [pl.ds_pos x h0] at hv; simp only [b0] at hv; omega

theorem ds_ne_scr (m : Fin 13) : ∀ x, pl.ds x ≠ d.scr pl.hT m := by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have ha := pl.har.1
  intro x h
  have hv := congrArg Fin.val h
  have hm := m.isLt
  have hs : (d.scr pl.hT m).val = d.scrV m.val := rfl
  have hsv : d.scrV m.val + 13 = d.B + m.val := by simp only [Dims.scrV, Dims.B]; omega
  rw [hs] at hv
  by_cases h0 : x.val = 0
  · rw [pl.ds_zero x h0] at hv; omega
  · rw [pl.ds_pos x h0] at hv; omega

theorem b0_ne_scr (m : Fin 13) : pl.b0 ≠ d.scr pl.hT m := by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  intro h
  have hv := congrArg Fin.val h
  have hm := m.isLt
  have hs : (d.scr pl.hT m).val = d.scrV m.val := rfl
  have hsv : d.scrV m.val + 13 = d.B + m.val := by simp only [Dims.scrV, Dims.B]; omega
  simp only [b0] at hv
  omega

theorem scr_ne : d.scr pl.hT 11 ≠ d.scr pl.hT 12 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Dims.scr, Dims.scrV] at hv
  omega

theorem pRl_val : (Dimension.pRl eR eV).val = 65 + 2*eR := by simp [Dimension.pRl, Dimension.o1]; omega
theorem pV_val : (Dimension.pV eR eV).val + 2 = Dimension.P eR eV := by simp [Dimension.pV, Dimension.P]
theorem pVl_val : (Dimension.pVl eR eV).val + 1 = Dimension.P eR eV := by
  simp [Dimension.pVl, Dimension.P]

theorem mask_false_lt (x : Fin T) (h : x.val < d.F) : pl.mask x = false := by
  simp only [Place.mask, decide_eq_false_iff_not]
  intro hh; omega

theorem mask_false_ge (x : Fin T) (h : d.U ≤ x.val) : pl.mask x = false := by
  simp only [Place.mask, decide_eq_false_iff_not]
  intro hh; omega

theorem mask_true (x : Fin T) (h1 : d.F ≤ x.val) (h2 : x.val < d.U) (h3 : x.val ≠ d.scrV 11)
    (h4 : x.val ≠ d.scrV 12) (h5 : x.val ≠ JB d eX pX gW + (65 + 2*eR))
    (h6 : x.val ≠ JB d eX pX gW + Dimension.P eR eV - 2) (h7 : x.val ≠ JB d eX pX gW + Dimension.P eR eV - 1) :
    pl.mask x = true := by
  simp only [Place.mask, decide_eq_true_eq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem mask_pq : pl.mask (pl.ds (Dimension.pq eR eV)) = false := by
  rw [pl.ds_zero _ rfl]; exact pl.mask_false_lt _ pl.har.1

theorem mask_port (x : Fin (Dimension.P eR eV)) (hx : x.val ≠ 0)
    (h : x.val = 65 + 2*eR ∨ x.val + 2 = Dimension.P eR eV ∨ x.val + 1 = Dimension.P eR eV) :
    pl.mask (pl.ds x) = false := by
  simp only [Place.mask, decide_eq_false_iff_not, pl.ds_pos x hx]
  intro hh; omega

theorem mask_pRl : pl.mask (pl.ds (Dimension.pRl eR eV)) = false :=
  pl.mask_port _ (by rw [pRl_val]; omega) (Or.inl pRl_val)
theorem mask_pV : pl.mask (pl.ds (Dimension.pV eR eV)) = false :=
  pl.mask_port _ (by have := pV_val (eR := eR) (eV := eV); have := Dimension.P_ge eR eV; omega)
    (Or.inr (Or.inl pV_val))
theorem mask_pVl : pl.mask (pl.ds (Dimension.pVl eR eV)) = false :=
  pl.mask_port _ (by have := pVl_val (eR := eR) (eV := eV); have := Dimension.P_ge eR eV; omega)
    (Or.inr (Or.inr pVl_val))
theorem mask_scr11 : pl.mask (d.scr pl.hT 11) = false := by
  simp only [Place.mask, decide_eq_false_iff_not]; intro hh; exact hh.2.2.1 rfl
theorem mask_scr12 : pl.mask (d.scr pl.hT 12) = false := by
  simp only [Place.mask, decide_eq_false_iff_not]; intro hh; exact hh.2.2.2.1 rfl

theorem ds_pV_eq : pl.ds (Dimension.pV eR eV) = pl.s2 2 := by
  have := pV_val (eR := eR) (eV := eV); have := Dimension.P_ge eR eV
  apply Fin.ext
  rw [pl.ds_pos _ (by omega)]
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 2
  rw [s2V_2]
  omega
theorem ds_pVl_eq : pl.ds (Dimension.pVl eR eV) = pl.s2 3 := by
  have := pVl_val (eR := eR) (eV := eV); have := Dimension.P_ge eR eV
  apply Fin.ext
  rw [pl.ds_pos _ (by omega)]
  show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 3
  rw [s2V_3]
  omega

/-- Below `F` and at or above `U`, the pipeline dock, `b0` and the clear tapes are absent. -/
theorem off_once (x : Fin T) (h : x.val < d.F ∨ d.U ≤ x.val) (hx : x ≠ pl.ar) :
    pl.mask x = false ∧ (∀ y, pl.ds y ≠ x) ∧ x ≠ pl.b0 ∧ x ≠ d.scr pl.hT 11 ∧ x ≠ d.scr pl.hT 12 := by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases h with h | h
    · exact pl.mask_false_lt x h
    · exact pl.mask_false_ge x h
  · intro y hy
    by_cases h0 : y.val = 0
    · rw [pl.ds_zero y h0] at hy; exact hx hy.symm
    · have := congrArg Fin.val hy
      rw [pl.ds_pos y h0] at this
      have := y.isLt; have := pl.hT
      omega
  · intro hb; have := congrArg Fin.val hb; simp only [b0] at this; omega
  · intro hb
    have h' : x.val = d.scrV 11 := congrArg Fin.val hb
    omega
  · intro hb
    have h' : x.val = d.scrV 12 := congrArg Fin.val hb
    omega

end Place

/-! ## 6. The post-`Once` machine's input, on `Once`'s exit -/

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

theorem post_input (q b Vv VL Rc : ℕ) (A A1 : Fin T → List Bool)
    (hAw : A pl.wd = List.replicate b true)
    (hlow : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 → A x = [])
    (hq : A1 pl.ar = UnaryTemplate.tape q)
    (hV : A1 (pl.ds (Dimension.pV eR eV)) = List.replicate Vv true)
    (hVl : A1 (pl.ds (Dimension.pVl eR eV)) = List.replicate VL false)
    (hd : A1 (d.scr pl.hT 11) = List.replicate Rc true) (hl : A1 (d.scr pl.hT 12) = List.replicate (Rc+2) false)
    (hm : ∀ y, pl.mask y = true → A1 y = List.replicate Rc false)
    (hoff : ∀ y, pl.mask y = false → (∀ x, pl.ds x ≠ y) → y ≠ pl.b0 → y ≠ d.scr pl.hT 11 →
      y ≠ d.scr pl.hT 12 → A1 y = A y) :
    ∀ j, A1 (pl.s2 j) = InitPost.input q b Vv VL Rc j := by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hmax := pl.ext.hX
  have hsep := pl.sep
  intro j
  have hj := j.isLt
  by_cases h0 : j.val = 0
  · have e : j = 0 := Fin.ext h0
    subst e; rw [← pl.at0, hq]; rfl
  by_cases h1 : j.val = 1
  · have e : j = 1 := Fin.ext h1
    subst e; rw [← pl.at1]
    obtain ⟨m, dsn, b0n, s11, s12⟩ := pl.off_once pl.wd (Or.inl pl.hwd.1) (fun h => pl.hne h.symm)
    rw [hoff _ m dsn b0n s11 s12, hAw]; rfl
  by_cases h2 : j.val = 2
  · have e : j = 2 := Fin.ext h2
    subst e; rw [← pl.ds_pV_eq, hV]; rfl
  by_cases h3 : j.val = 3
  · have e : j = 3 := Fin.ext h3
    subst e; rw [← pl.ds_pVl_eq, hVl]; rfl
  by_cases h4 : j.val = 4
  · have e : j = 4 := Fin.ext h4
    subst e; rw [← pl.at4, hd]; rfl
  by_cases h5 : j.val = 5
  · have e : j = 5 := Fin.ext h5
    subst e; rw [← pl.at5, hl]; rfl
  have hin : InitPost.input q b Vv VL Rc j = if j.val < 12 then [] else List.replicate Rc false := by
    simp only [InitPost.input, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  rw [hin]
  by_cases h12' : j.val < 12
  · rw [if_pos h12']
    have hv : (pl.s2 j).val = 272 + j.val := by
      rw [s2_val, s2V_rew d eX pX gW _ pl.ar.val pl.wd.val j.val (by omega) h12']
    have hne : pl.s2 j ≠ pl.ar := fun h => by
      have := congrArg Fin.val h; have := pl.har.2; omega
    obtain ⟨m, dsn, b0n, s11, s12⟩ := pl.off_once (pl.s2 j) (Or.inl (by omega)) hne
    rw [hoff _ m dsn b0n s11 s12]
    exact hlow _ (by omega) (by omega)
  · rw [if_neg h12']
    have hin2 := s2V_in d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val j.val hj
    have hdec := dec_s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val hsep j.val
    apply hm
    rw [← s2_val] at hin2 hdec
    have ha := pl.har; have hw := pl.hwd
    have hpR : 65 + 2*eR < Dimension.P eR eV - 2 := by
      simp only [Dimension.P, Dimension.o2, Dimension.o1]; omega
    -- `j ≥ 12`: the value is in one of the high blocks
    have hge : (j.val < 17 ∧ (pl.s2 j).val = d.B + 2 + j.val) ∨
        (17 ≤ j.val ∧ j.val < 22 ∧ (pl.s2 j).val = d.B + 19 + restPc eX pX gW + (j.val - 17)) ∨
        (22 ≤ j.val ∧ j.val < 32 ∧ (pl.s2 j).val = d.F + d.rt + j.val - 19) ∨
        (32 ≤ j.val ∧ (pl.s2 j).val = JB d eX pX gW + Dimension.P eR eV + 1 + (j.val - 32)) := by
      rw [s2_val]
      by_cases a17 : j.val < 17
      · exact Or.inl ⟨a17, s2V_cs d eX pX gW _ _ _ j.val (by omega) a17⟩
      by_cases a22 : j.val < 22
      · exact Or.inr (Or.inl ⟨by omega, a22, s2V_rs d eX pX gW _ _ _ j.val (by omega) a22⟩)
      by_cases a32 : j.val < 32
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, a32, s2V_enc d eX pX gW _ _ _ j.val (by omega) a32⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, s2V_junk d eX pX gW _ _ _ j.val (by omega)⟩))
    have hsv11 : d.scrV 11 + 2 = d.B := h11
    have hsv12 : d.scrV 12 + 1 = d.B := h12
    have hU' : d.U = d.B + d.res := hU
    refine pl.mask_true _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · rcases hge with ⟨r1, e⟩ | ⟨r1, r2, e⟩ | ⟨r1, r2, e⟩ | ⟨r1, e⟩ <;> rw [e] <;> omega

end Place

/-! ## 7. The exit facts -/

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

theorem head_slot (H : Fin T → ℕ) (j : Fin 323) :
    dockH pl.s2 H InitPost.outH (pl.s2 j) = if 13 ≤ j.val ∧ j.val ≤ 16 then 1 else 0 := by
  rw [dockH_slot pl.s2 pl.s2_inj]
  exact InitPost.outH_val j

theorem off_dock (H : Fin T → ℕ) (A1 : Fin T → List Bool) (W : Fin 323 → List Bool) (x : Fin T)
    (hx : ¬ InS2 d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val x.val) :
    install pl.s2 A1 W x = A1 x ∧ dockH pl.s2 H InitPost.outH x = H x :=
  ⟨install_other pl.s2 A1 W x (pl.s2_ne x hx), dockH_other pl.s2 H InitPost.outH x (pl.s2_ne x hx)⟩

end Place

/-! ## 8. The exit of the post-`Once` machine, as one proposition -/

/-- `InitPost.post_run`'s conclusion (without the `Step`), verbatim. -/
def PostOut (L cS cR q b V Rc : ℕ) (W : Fin 323 → List Bool) : Prop :=
  W 0 = UnaryTemplate.tape q ∧ W 1 = List.replicate b true ∧
  W 4 = List.replicate Rc true ∧ W 5 = List.replicate (Rc+2) false ∧
  W 6 = List.replicate V true ∧ W 7 = List.replicate V false ∧
  W 12 = ZeroPadding.pad Rc (List.replicate (3*(normalizedLiveCount q L+2+1) +
    ((q - normalizedLiveCount q L+1)/2 + (q - normalizedLiveCount q L+1)/2)) true) ∧
  W 13 = ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(V+1))) ∧
  W 14 = ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(V+1))) ∧
  W 15 = ZeroPadding.pad Rc (UnaryTemplate.tape (V+1)) ∧
  W 16 = ZeroPadding.pad Rc (UnaryTemplate.tape b) ∧
  W 17 = ZeroPadding.pad Rc (List.replicate (q / InitSlopes.dv L q * InitPost.Ms L q) true) ∧
  W 18 = ZeroPadding.pad Rc (List.replicate (InitPost.Ms L q) true) ∧
  W 19 = List.replicate Rc false ∧
  W 20 = ZeroPadding.pad Rc (List.replicate b true) ∧
  W 21 = ZeroPadding.pad Rc (List.replicate q true) ∧
  W 22 = ZeroPadding.pad Rc (frame (SignedSortKey.binary (2*b+2) 0)) ∧
  W 23 = List.replicate Rc false ∧ W 24 = List.replicate Rc false ∧
  W 25 = ZeroPadding.pad Rc (List.replicate (InitEnc.rr b+2) false) ∧
  W 26 = ZeroPadding.pad Rc (List.replicate (InitEnc.rr b+1) true) ∧
  W 27 = ZeroPadding.pad Rc (List.replicate (InitEnc.rr b+2) false) ∧
  W 28 = ZeroPadding.pad Rc (List.replicate (40*b+56) false) ∧
  W 29 = ZeroPadding.pad Rc (List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false) ∧
  W 30 = ZeroPadding.pad Rc (UnaryTemplate.tape (20*b+22)) ∧
  W 31 = ZeroPadding.pad Rc (List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false) ∧
  W 2 = List.replicate Rc false ∧ W 3 = List.replicate Rc false ∧
  (∀ i : Fin 323, 12 ≤ i.val → Rc ≤ (W i).length)

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

/-- The residents, from the post-`Once` machine's exit. -/
theorem out_res (L cS cR q b Rc Vv : ℕ) (hRc : 2 ≤ Rc) (H : Fin T → ℕ) (A1 : Fin T → List Bool)
    (W : Fin 323 → List Bool) (hW : PostOut L cS cR q b Vv Rc W) :
    let A' := install pl.s2 A1 W
    let H' := dockH pl.s2 H InitPost.outH
    (A' (d.scr pl.hT 11) = List.replicate Rc true ∧ H' (d.scr pl.hT 11) = 0) ∧
    (A' (d.scr pl.hT 12) = List.replicate (Rc+2) false ∧ H' (d.scr pl.hT 12) = 0) ∧
    (A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = List.replicate Vv true ∧
      H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = 0) ∧
    (A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = List.replicate Vv false ∧
      H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = 0) ∧
    (A' (Dims.csSlots pl.ext.rest.ext pl.hT 2) = ZeroPadding.pad Rc (List.replicate (U0 L q) true) ∧
      H' (Dims.csSlots pl.ext.rest.ext pl.hT 2) = 0) ∧
    (A' (Dims.drvSlots pl.ext.rest.ext pl.hT 0) = ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(Vv+1))) ∧
      H' (Dims.drvSlots pl.ext.rest.ext pl.hT 0) = 1) ∧
    (A' (Dims.drvSlots pl.ext.rest.ext pl.hT 1) = ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(Vv+1))) ∧
      H' (Dims.drvSlots pl.ext.rest.ext pl.hT 1) = 1) ∧
    (A' (Dims.drvSlots pl.ext.rest.ext pl.hT 2) = ZeroPadding.pad Rc (UnaryTemplate.tape (Vv+1)) ∧
      H' (Dims.drvSlots pl.ext.rest.ext pl.hT 2) = 1) ∧
    (A' (Dims.drvSlots pl.ext.rest.ext pl.hT 4) = ZeroPadding.pad Rc (UnaryTemplate.tape b) ∧
      H' (Dims.drvSlots pl.ext.rest.ext pl.hT 4) = 1) ∧
    (A' (Dims.rsT pl.ext.rest pl.hT 0) = ZeroPadding.pad Rc (List.replicate (Mb L q) true) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 0) = 0) ∧
    (A' (Dims.rsT pl.ext.rest pl.hT 1) = ZeroPadding.pad Rc (List.replicate (InitPost.Ms L q) true) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 1) = 0) ∧
    (A' (Dims.rsT pl.ext.rest pl.hT 2) = ZeroPadding.pad Rc (UnaryTemplate.tape 0) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 2) = 0) ∧
    (A' (Dims.rsT pl.ext.rest pl.hT 3) = ZeroPadding.pad Rc (List.replicate b true) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 3) = 0) ∧
    (A' (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 4) = 0) := by
  intro A' H'
  obtain ⟨w0, w1, w4, w5, w6, w7, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26,
    w27, w28, w29, w30, w31, w2, w3, wl⟩ := hW
  have sl : ∀ j, A' (pl.s2 j) = W j := fun j => install_slot pl.s2 pl.s2_inj A1 W j
  have hd : ∀ j, H' (pl.s2 j) = if 13 ≤ j.val ∧ j.val ≤ 16 then 1 else 0 := fun j => pl.head_slot H j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pl.at4, sl, hd]; exact ⟨w4, rfl⟩
  · rw [pl.at5, sl, hd]; exact ⟨w5, rfl⟩
  · rw [pl.at6, sl, hd]; exact ⟨w6, rfl⟩
  · rw [pl.at7, sl, hd]; exact ⟨w7, rfl⟩
  · rw [pl.at12, sl, hd]; exact ⟨w12, rfl⟩
  · rw [pl.at13, sl, hd]; exact ⟨w13, rfl⟩
  · rw [pl.at14, sl, hd]; exact ⟨w14, rfl⟩
  · rw [pl.at15, sl, hd]; exact ⟨w15, rfl⟩
  · rw [pl.at16, sl, hd]; exact ⟨w16, rfl⟩
  · rw [pl.atRs 0, sl, hd]; exact ⟨w17, rfl⟩
  · rw [pl.atRs 1, sl, hd]; exact ⟨w18, rfl⟩
  · rw [pl.atRs 2, sl, hd]
    refine ⟨w19.trans ?_, rfl⟩
    exact (ExtDecompositionBatch.pad_replicate_false Rc 2 hRc).symm
  · rw [pl.atRs 3, sl, hd]; exact ⟨w20, rfl⟩
  · rw [pl.atRs 4, sl, hd]; exact ⟨w21, rfl⟩

/-- The eight `enc`/`app` constants in the consumer's form, and the two blank `enc` tapes. -/
theorem out_enc (L cS cR q b Rc Vv : ℕ) (H : Fin T → ℕ) (A1 : Fin T → List Bool)
    (W : Fin 323 → List Bool) (hW : PostOut L cS cR q b Vv Rc W) :
    let A' := install pl.s2 A1 W
    let H' := dockH pl.s2 H InitPost.outH
    (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
      (A' (Dims.encT (d := d) pl.hT 3) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 3) ∧
        H' (Dims.encT (d := d) pl.hT 3) = 0) ∧
      (A' (Dims.encT (d := d) pl.hT 6) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 7) ∧
        H' (Dims.encT (d := d) pl.hT 6) = 0) ∧
      (A' (Dims.encT (d := d) pl.hT 7) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 8) ∧
        H' (Dims.encT (d := d) pl.hT 7) = 0) ∧
      (A' (Dims.encT (d := d) pl.hT 8) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 9) ∧
        H' (Dims.encT (d := d) pl.hT 8) = 0) ∧
      (A' (Dims.encT (d := d) pl.hT 9) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 10) ∧
        H' (Dims.encT (d := d) pl.hT 9) = 0)) ∧
    (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
      (A' (Dims.encT (d := d) pl.hT 10) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
        (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 2) ∧
        H' (Dims.encT (d := d) pl.hT 10) = 0) ∧
      (A' (Dims.encT (d := d) pl.hT 11) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
        (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 4) ∧
        H' (Dims.encT (d := d) pl.hT 11) = 0) ∧
      (A' (Dims.encT (d := d) pl.hT 12) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
        (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 5) ∧
        H' (Dims.encT (d := d) pl.hT 12) = 0)) ∧
    (∀ kk : Fin 13, (kk.val = 4 ∨ kk.val = 5) →
      A' (Dims.encT (d := d) pl.hT kk) = List.replicate Rc false ∧ H' (Dims.encT (d := d) pl.hT kk) = 0) := by
  intro A' H'
  obtain ⟨w0, w1, w4, w5, w6, w7, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26,
    w27, w28, w29, w30, w31, w2, w3, wl⟩ := hW
  have sl : ∀ j, A' (pl.s2 j) = W j := fun j => install_slot pl.s2 pl.s2_inj A1 W j
  have hd : ∀ j, H' (pl.s2 j) = if 13 ≤ j.val ∧ j.val ≤ 16 then 1 else 0 := fun j => pl.head_slot H j
  refine ⟨fun en old => ⟨?_, ?_, ?_, ?_, ?_⟩, fun en xs => ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [pl.atEnc 3 (by decide), sl, hd]; exact ⟨w22, rfl⟩
  · rw [pl.atEnc 6 (by decide), sl, hd]; exact ⟨w25, rfl⟩
  · rw [pl.atEnc 7 (by decide), sl, hd]; exact ⟨w26, rfl⟩
  · rw [pl.atEnc 8 (by decide), sl, hd]; exact ⟨w27, rfl⟩
  · rw [pl.atEnc 9 (by decide), sl, hd]; exact ⟨w28, rfl⟩
  · rw [pl.atEnc 10 (by decide), sl, hd]; exact ⟨w29, rfl⟩
  · rw [pl.atEnc 11 (by decide), sl, hd]; exact ⟨w30, rfl⟩
  · rw [pl.atEnc 12 (by decide), sl, hd]; exact ⟨w31, rfl⟩
  · intro kk hk
    rcases hk with hk | hk
    · have e : kk = 4 := Fin.ext hk
      subst e; rw [pl.atEnc 4 (by decide), sl, hd]; exact ⟨w23, rfl⟩
    · have e : kk = 5 := Fin.ext hk
      subst e; rw [pl.atEnc 5 (by decide), sl, hd]; exact ⟨w24, rfl⟩

end Place

/-! ## 9. The frame -/

/-- `Rc`'s exact log from the pipeline is at least `Rc` long. -/
theorem rcLog_long (eR L C q : ℕ) :
    Once.Rc eR L C q ≤ (List.replicate (C*(q+1)^eR*(2*2^(q - normalizedLiveCount q L)+3)+2) false).length := by
  rw [List.length_replicate]
  unfold Once.Rc RuntimeShape.tableClass
  have h1 : 2^(q - normalizedLiveCount q L) ≤ 2*2^(q - normalizedLiveCount q L)+3 := by omega
  calc C*((q+1)^eR*2^(q - normalizedLiveCount q L)) = C*(q+1)^eR*2^(q - normalizedLiveCount q L) := by ring
    _ ≤ C*(q+1)^eR*(2*2^(q - normalizedLiveCount q L)+3) := Nat.mul_le_mul_left _ h1
    _ ≤ _ := by omega

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

theorem out_frame (L cS cR q b Rc Vv : ℕ) (H : Fin T → ℕ) (A A1 : Fin T → List Bool)
    (W : Fin 323 → List Bool) (hW : PostOut L cS cR q b Vv Rc W)
    (hAr : A pl.ar = UnaryTemplate.tape q) (hHr : H pl.ar = 0)
    (hAw : A pl.wd = List.replicate b true) (hHw : H pl.wd = 0)
    (hF : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A x = [] ∧ H x = 0)
    (hm : ∀ y, pl.mask y = true → A1 y = List.replicate Rc false)
    (hRl : Rc ≤ (A1 (pl.ds (Dimension.pRl eR eV))).length)
    (hoff : ∀ y, pl.mask y = false → (∀ x, pl.ds x ≠ y) → y ≠ pl.b0 → y ≠ d.scr pl.hT 11 →
      y ≠ d.scr pl.hT 12 → A1 y = A y) :
    let A' := install pl.s2 A1 W
    let H' := dockH pl.s2 H InitPost.outH
    (∀ x : Fin T, d.F ≤ x.val → x.val < d.U → ¬ Kept d eX pX gW X x.val →
      A' x = List.replicate Rc false ∧ H' x = 0) ∧
    (∀ x : Fin T, JB d eX pX gW ≤ x.val → x.val < JB d eX pX gW + X → Rc ≤ (A' x).length ∧ H' x = 0) ∧
    (∀ x : Fin T, x.val < d.F → (x.val < 278 ∨ 284 ≤ x.val) → A' x = A x ∧ H' x = H x) ∧
    (∀ x : Fin T, 278 ≤ x.val → x.val < 284 → H' x = 0) ∧
    (∀ x : Fin T, d.U ≤ x.val → A' x = A x ∧ H' x = H x) := by
  intro A' H'
  obtain ⟨w0, w1, w4, w5, w6, w7, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26,
    w27, w28, w29, w30, w31, w2, w3, wl⟩ := hW
  obtain ⟨hF', hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hX := pl.ext.hX
  have hjunk := pl.ext.hjunk
  have ha := pl.har
  have hw := pl.hwd
  have hpR : 65 + 2*eR < Dimension.P eR eV - 2 := by
    simp only [Dimension.P, Dimension.o2, Dimension.o1]; omega
  have sl : ∀ j, A' (pl.s2 j) = W j := fun j => install_slot pl.s2 pl.s2_inj A1 W j
  have hd : ∀ j, H' (pl.s2 j) = if 13 ≤ j.val ∧ j.val ≤ 16 then 1 else 0 := fun j => pl.head_slot H j
  have hAa : ∀ x : Fin T, x.val = pl.ar.val → x = pl.ar := fun x h => Fin.ext h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- blank
    intro x h1 h2 hk
    have hn : ¬ InS2 d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val x.val := by
      unfold Kept at hk; unfold InS2; intro h
      rcases h with h | h | h | h | h | h | h | h | h | h | h <;> omega
    obtain ⟨o1, o2⟩ := pl.off_dock H A1 W x hn
    refine ⟨o1.trans (hm x (pl.mask_true x h1 h2 ?_ ?_ ?_ ?_ ?_)), o2.trans (hF x h1 h2).2⟩
    all_goals (unfold Kept at hk; omega)
  · -- the workspace
    intro x h1 h2
    have hxU : x.val < d.U := by omega
    by_cases e2 : x.val = JB d eX pX gW + Dimension.P eR eV - 2
    · have ex : x = pl.s2 2 := Fin.ext (by
        show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 2
        rw [s2V_2]; exact e2)
      rw [ex, sl, hd, w2]; exact ⟨by simp, rfl⟩
    by_cases e3 : x.val = JB d eX pX gW + Dimension.P eR eV - 1
    · have ex : x = pl.s2 3 := Fin.ext (by
        show _ = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val 3
        rw [s2V_3]; exact e3)
      rw [ex, sl, hd, w3]; exact ⟨by simp, rfl⟩
    by_cases e4 : JB d eX pX gW + Dimension.P eR eV + 1 ≤ x.val ∧ x.val < JB d eX pX gW + Dimension.P eR eV + 292
    · have ex : x = pl.s2 ⟨x.val - (JB d eX pX gW + Dimension.P eR eV + 1) + 32, by omega⟩ := Fin.ext (by
        show x.val = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val
          (x.val - (JB d eX pX gW + Dimension.P eR eV + 1) + 32)
        rw [s2V_junk d eX pX gW _ _ _ _ (by omega)]; omega)
      rw [ex, sl, hd]
      have k1 : 12 ≤ x.val - (JB d eX pX gW + Dimension.P eR eV + 1) + 32 := by omega
      have k2 : ¬ (13 ≤ x.val - (JB d eX pX gW + Dimension.P eR eV + 1) + 32 ∧
          x.val - (JB d eX pX gW + Dimension.P eR eV + 1) + 32 ≤ 16) := by omega
      exact ⟨wl _ k1, if_neg k2⟩
    have hn : ¬ InS2 d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val x.val := by
      unfold InS2; intro h
      rcases h with h | h | h | h | h | h | h | h | h | h | h <;> omega
    obtain ⟨o1, o2⟩ := pl.off_dock H A1 W x hn
    refine ⟨?_, o2.trans (hF x (by omega) hxU).2⟩
    have o1' : A' x = A1 x := o1
    rw [o1']
    by_cases eR' : x.val = JB d eX pX gW + (65 + 2*eR)
    · have ex : x = pl.ds (Dimension.pRl eR eV) := Fin.ext (by
        rw [pl.ds_pos _ (by rw [pRl_val]; omega), pRl_val]; exact eR')
      rw [ex]; exact hRl
    · rw [hm x (pl.mask_true x (by omega) hxU (by omega) (by omega) eR' e2 e3)]; simp
  · -- below `F`
    intro x h1 h2
    by_cases ea : x.val = pl.ar.val
    · have ex : x = pl.s2 0 := (hAa x ea).trans pl.at0
      rw [ex, sl, hd, w0, ← pl.at0, hAr, hHr]; exact ⟨rfl, rfl⟩
    by_cases ew : x.val = pl.wd.val
    · have ex : x = pl.s2 1 := (Fin.ext ew).trans pl.at1
      rw [ex, sl, hd, w1, ← pl.at1, hAw, hHw]; exact ⟨rfl, rfl⟩
    have hn : ¬ InS2 d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val x.val := by
      unfold InS2; intro h
      rcases h with h | h | h | h | h | h | h | h | h | h | h <;> omega
    obtain ⟨o1, o2⟩ := pl.off_dock H A1 W x hn
    obtain ⟨m, dsn, b0n, s11, s12⟩ := pl.off_once x (Or.inl h1) (fun h => ea (congrArg Fin.val h))
    exact ⟨o1.trans (hoff x m dsn b0n s11 s12), o2⟩
  · -- the rewind tapes' heads
    intro x h1 h2
    have ex : x = pl.s2 ⟨x.val - 272, by omega⟩ := Fin.ext (by
      show x.val = s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val (x.val - 272)
      rw [s2V_rew d eX pX gW _ _ _ _ (by omega) (by omega)]; omega)
    rw [ex, hd]
    have k2 : ¬ (13 ≤ x.val - 272 ∧ x.val - 272 ≤ 16) := by omega
    exact if_neg k2
  · -- the loop counter and above
    intro x h1
    have hn : ¬ InS2 d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val x.val := by
      unfold InS2; intro h
      rcases h with h | h | h | h | h | h | h | h | h | h | h <;> omega
    obtain ⟨o1, o2⟩ := pl.off_dock H A1 W x hn
    obtain ⟨m, dsn, b0n, s11, s12⟩ := pl.off_once x (Or.inr h1) (fun h => by
      have := congrArg Fin.val h; omega)
    exact ⟨o1.trans (hoff x m dsn b0n s11 s12), o2⟩

end Place

/-! ## 10. The run -/

namespace Place

end Place

/-! ## 11. The consumer's side conditions at the uniform choices -/


end
end NearCubicWires.SourceConstruction.InitRun
end
