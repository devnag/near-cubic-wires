import Proof.SourceAssembly.SourceInitRun
import Proof.SourceAssembly.SourceRefresh

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

/-! ## 1. The transfer machine -/

/-- The four driver heads (`drv 0 1 2 4 = B+15 .. B+18`) move left by one. -/
def backDirs (d : Dims) (T : Nat) : Fin T → HeadMove := fun x =>
  if d.B + 15 ≤ x.val ∧ x.val ≤ d.B + 18 then HeadMove.left else HeadMove.stay

def backM (d : Dims) (T : Nat) := DecompositionCountPosition.move (backDirs d T)

/-- The heads after the move. -/
def backH (d : Dims) {T : Nat} (H : Fin T → ℕ) : Fin T → ℕ := fun x => (backDirs d T x).apply (H x)

/-- The five master words, in `Inv`'s order `U0, S, Rw, B, v` (`S = cS(V+1)`, `Rw = cR(V+1)`, `B = V+1`, `v = b`). -/
def masterW (L cS cR q b Rc Vv : ℕ) : Fin 5 → List Bool :=
  ![ZeroPadding.pad Rc (List.replicate (U0 L q) true), ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(Vv+1))),
    ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(Vv+1))), ZeroPadding.pad Rc (UnaryTemplate.tape (Vv+1)),
    ZeroPadding.pad Rc (UnaryTemplate.tape b)]

/-- Each master is exactly `Rc` long once its content fits (S R-S2: `U0 ≤ Rc`, `S+2, Rw+2, B+2, v+2 ≤ Rc`). -/
theorem masterW_length (L cS cR q b Rc Vv : ℕ) (hU : U0 L q ≤ Rc) (hS : cS*(Vv+1)+2 ≤ Rc)
    (hR : cR*(Vv+1)+2 ≤ Rc) (hB : Vv+1+2 ≤ Rc) (hv : b+2 ≤ Rc) :
    ∀ i, (masterW L cS cR q b Rc Vv i).length = Rc := by
  intro i
  fin_cases i <;> simp [masterW, UnaryTemplate.tape] <;> omega

/-- The transfer's cost. -/
def xferCost (Rc : ℕ) : ℕ :=
  1 + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + ((2*Rc+4) + 1 + (2*Rc+4)))))

/-- S's layout fact `RestExt2` (ten prologue residents) holds on the init's placement. -/
theorem Place.ext2 {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) :
    d.RestExt2 eX pX gW := ⟨pl.ext.rest, by have := pl.ext.hjunk; omega⟩

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

/-- The copy of target `i` onto master `i`. -/
def saveM (i : Fin 5) :=
  RecoveryFocus.machine (![Dims.rfT pl.ext2 pl.hT i, Dims.mT pl.ext2 pl.hT i, d.scr pl.hT 11, d.scr pl.hT 12] :
    Fin 4 → Fin T) RecoveryBoundedTapeCopy.machine

/-- **The transfer machine**: heads back, then five copies. -/
def xferMachine :=
  Composition.machine (backM d T) (Composition.machine (pl.saveM 0) (Composition.machine (pl.saveM 1)
    (Composition.machine (pl.saveM 2) (Composition.machine (pl.saveM 3) (pl.saveM 4)))))

def init2Cost (L C cVc cS cR q b : ℕ) : ℕ :=
  pl.initCost L C cVc cS cR q b + 1 + xferCost (Once.Rc eR L C q)

/-! ## 2. Values -/

theorem mT_val (i : Fin 5) : (Dims.mT pl.ext2 pl.hT i).val = d.B + 19 + restPc eX pX gW + 5 + i.val := rfl
theorem rfT_val (i : Fin 5) : (Dims.rfT pl.ext2 pl.hT i).val = d.B + 14 + i.val := rfl

theorem scr_vals : (d.scr pl.hT 11).val + 2 = d.B ∧ (d.scr pl.hT 12).val + 1 = d.B := by
  obtain ⟨_, _, h11, h12, _⟩ := lay pl.ext
  exact ⟨h11, h12⟩

/-- A tape off the master block is off every master. -/
theorem off_mT (x : Fin T)
    (hx : x.val < d.B + 19 + restPc eX pX gW + 5 ∨ d.B + 19 + restPc eX pX gW + 10 ≤ x.val) :
    ∀ i, Dims.mT pl.ext2 pl.hT i ≠ x := by
  intro i h
  have hv := congrArg Fin.val h
  rw [pl.mT_val] at hv
  have := i.isLt
  omega

/-- A tape off the four drivers keeps its head through the move. -/
theorem backH_off (H : Fin T → ℕ) (x : Fin T) (hx : x.val < d.B + 15 ∨ d.B + 18 < x.val) :
    backH d H x = H x := by
  have h : ¬ (d.B + 15 ≤ x.val ∧ x.val ≤ d.B + 18) := by omega
  simp only [backH, backDirs, if_neg h]
  rfl

theorem mT_ne_rfT' (i k : Fin 5) : Dims.mT pl.ext2 pl.hT i ≠ Dims.rfT pl.ext2 pl.hT k := by
  intro h
  have hv := congrArg Fin.val h
  rw [pl.mT_val, pl.rfT_val] at hv
  have := i.isLt; have := k.isLt
  omega

theorem scr_ne_rfT' (k : Fin 5) : d.scr pl.hT 11 ≠ Dims.rfT pl.ext2 pl.hT k ∧
    d.scr pl.hT 12 ≠ Dims.rfT pl.ext2 pl.hT k := by
  obtain ⟨h11, h12⟩ := pl.scr_vals
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · have hv := congrArg Fin.val h
    rw [pl.rfT_val] at hv
    omega

theorem scr_ne_mT' (k : Fin 5) : d.scr pl.hT 11 ≠ Dims.mT pl.ext2 pl.hT k ∧
    d.scr pl.hT 12 ≠ Dims.mT pl.ext2 pl.hT k := by
  obtain ⟨h11, h12⟩ := pl.scr_vals
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · have hv := congrArg Fin.val h
    rw [pl.mT_val] at hv
    omega

theorem scr11_ne_12 : d.scr pl.hT 11 ≠ d.scr pl.hT 12 := by
  obtain ⟨h11, h12⟩ := pl.scr_vals
  intro h
  have := congrArg Fin.val h
  omega

/-! ## 3. The transfer run -/

/-- **The transfer.** From the five words on the targets `rfT 0..4` (head 0 on `cs 2`, heads 1 on the four drivers), blank
masters and the resident clear driver/log: the masters hold the five words at head 0, the target heads are 0, and nothing
else changes (words off the masters, heads off the targets). -/
theorem xfer_run (Rc : ℕ) (Mw : Fin 5 → List Bool) (hMw : ∀ i, (Mw i).length = Rc)
    (H : Fin T → ℕ) (A : Fin T → List Bool)
    (ht : ∀ i, A (Dims.rfT pl.ext2 pl.hT i) = Mw i)
    (htH0 : H (Dims.rfT pl.ext2 pl.hT 0) = 0)
    (htH : ∀ i : Fin 5, i.val ≠ 0 → H (Dims.rfT pl.ext2 pl.hT i) = 1)
    (hm : ∀ i, A (Dims.mT pl.ext2 pl.hT i) = List.replicate Rc false)
    (hmH : ∀ i, H (Dims.mT pl.ext2 pl.hT i) = 0)
    (hdrv : A (d.scr pl.hT 11) = List.replicate Rc true) (hdrvH : H (d.scr pl.hT 11) = 0)
    (hlg : A (d.scr pl.hT 12) = List.replicate (Rc+2) false) (hlgH : H (d.scr pl.hT 12) = 0) :
    ∃ A' : Fin T → List Bool, Step pl.xferMachine (xferCost Rc) H A (backH d H) A' ∧
      (∀ i, A' (Dims.mT pl.ext2 pl.hT i) = Mw i) ∧
      (∀ x, (∀ i, Dims.mT pl.ext2 pl.hT i ≠ x) → A' x = A x) ∧
      (∀ i, backH d H (Dims.rfT pl.ext2 pl.hT i) = 0) ∧
      (∀ x, (∀ i, Dims.rfT pl.ext2 pl.hT i ≠ x) → backH d H x = H x) := by
  classical
  -- 1. the move
  obtain ⟨rr, hr, hf, _⟩ := DecompositionCountPosition.move_run (backDirs d T) H A
  have sM : Step (backM d T) 1 H A (fun x => ((backDirs d T) x).apply (H x)) A :=
    Step.of_run hr (by rw [hf]) (congrArg Configuration.tapes hf)
  set H2 := backH d H with hH2
  have H2t : ∀ i, H2 (Dims.rfT pl.ext2 pl.hT i) = 0 := by
    intro i
    by_cases h0 : i.val = 0
    · have e : i = 0 := Fin.ext h0
      subst e
      rw [hH2, backH_off H _ (by rw [pl.rfT_val]; omega)]
      exact htH0
    · have hin : d.B + 15 ≤ (Dims.rfT pl.ext2 pl.hT i).val ∧ (Dims.rfT pl.ext2 pl.hT i).val ≤ d.B + 18 := by
        rw [pl.rfT_val]; have := i.isLt; omega
      simp only [hH2, backH, backDirs, if_pos hin, htH i h0]
      rfl
  have H2o : ∀ x, (∀ i, Dims.rfT pl.ext2 pl.hT i ≠ x) → H2 x = H x := by
    intro x hx
    have hxv : ¬ (d.B + 14 ≤ x.val ∧ x.val ≤ d.B + 18) := by
      intro h
      exact hx ⟨x.val - (d.B + 14), by omega⟩ (Fin.ext (by rw [pl.rfT_val]; simp; omega))
    exact backH_off H x (by omega)
  have H2m : ∀ i, H2 (Dims.mT pl.ext2 pl.hT i) = 0 := fun i =>
    (H2o _ (fun k h => pl.mT_ne_rfT' i k h.symm)).trans (hmH i)
  have H2d : H2 (d.scr pl.hT 11) = 0 := (H2o _ (fun k h => (pl.scr_ne_rfT' k).1 h.symm)).trans hdrvH
  have H2l : H2 (d.scr pl.hT 12) = 0 := (H2o _ (fun k h => (pl.scr_ne_rfT' k).2 h.symm)).trans hlgH
  -- 2. the five copies (heads `H2` throughout)
  have cp : ∀ (i : Fin 5) (B0 : Fin T → List Bool), B0 (Dims.rfT pl.ext2 pl.hT i) = Mw i →
      B0 (Dims.mT pl.ext2 pl.hT i) = List.replicate Rc false → B0 (d.scr pl.hT 11) = List.replicate Rc true →
      B0 (d.scr pl.hT 12) = List.replicate (Rc+2) false →
      ∃ B1, Step (pl.saveM i) (2*Rc+4) H2 B0 H2 B1 ∧ B1 (Dims.mT pl.ext2 pl.hT i) = Mw i ∧
        (∀ x, x ≠ Dims.mT pl.ext2 pl.hT i → B1 x = B0 x) := by
    intro i B0 b1 b2 b3 b4
    exact Rest.copy_one _ _ _ _ (fun h => pl.mT_ne_rfT' i i h.symm) (fun h => (pl.scr_ne_rfT' i).1 h.symm)
      (fun h => (pl.scr_ne_rfT' i).2 h.symm) (fun h => (pl.scr_ne_mT' i).1 h.symm)
      (fun h => (pl.scr_ne_mT' i).2 h.symm) pl.scr11_ne_12 Rc (Mw i) (hMw i) H2 B0 b1 b2 b3 b4
      (H2t i) (H2m i) H2d H2l
  have mne : ∀ i k : Fin 5, i ≠ k → Dims.mT pl.ext2 pl.hT i ≠ Dims.mT pl.ext2 pl.hT k :=
    fun i k h hh => h (Dims.mT_injective pl.ext2 pl.hT hh)
  have n11 : ∀ k, d.scr pl.hT 11 ≠ Dims.mT pl.ext2 pl.hT k := fun k => (pl.scr_ne_mT' k).1
  have n12 : ∀ k, d.scr pl.hT 12 ≠ Dims.mT pl.ext2 pl.hT k := fun k => (pl.scr_ne_mT' k).2
  have rm : ∀ i k, Dims.rfT pl.ext2 pl.hT i ≠ Dims.mT pl.ext2 pl.hT k := fun i k h => pl.mT_ne_rfT' k i h.symm
  obtain ⟨B1, s1, b1t, b1o⟩ := cp 0 A (ht 0) (hm 0) hdrv hlg
  obtain ⟨B2, s2, b2t, b2o⟩ := cp 1 B1 ((b1o _ (rm 1 0)).trans (ht 1))
    ((b1o _ (mne 1 0 (by decide))).trans (hm 1)) ((b1o _ (n11 0)).trans hdrv) ((b1o _ (n12 0)).trans hlg)
  obtain ⟨B3, s3, b3t, b3o⟩ := cp 2 B2
    ((b2o _ (rm 2 1)).trans ((b1o _ (rm 2 0)).trans (ht 2)))
    ((b2o _ (mne 2 1 (by decide))).trans ((b1o _ (mne 2 0 (by decide))).trans (hm 2)))
    ((b2o _ (n11 1)).trans ((b1o _ (n11 0)).trans hdrv)) ((b2o _ (n12 1)).trans ((b1o _ (n12 0)).trans hlg))
  obtain ⟨B4, s4, b4t, b4o⟩ := cp 3 B3
    ((b3o _ (rm 3 2)).trans ((b2o _ (rm 3 1)).trans ((b1o _ (rm 3 0)).trans (ht 3))))
    ((b3o _ (mne 3 2 (by decide))).trans ((b2o _ (mne 3 1 (by decide))).trans
      ((b1o _ (mne 3 0 (by decide))).trans (hm 3))))
    ((b3o _ (n11 2)).trans ((b2o _ (n11 1)).trans ((b1o _ (n11 0)).trans hdrv)))
    ((b3o _ (n12 2)).trans ((b2o _ (n12 1)).trans ((b1o _ (n12 0)).trans hlg)))
  obtain ⟨B5, s5, b5t, b5o⟩ := cp 4 B4
    ((b4o _ (rm 4 3)).trans ((b3o _ (rm 4 2)).trans ((b2o _ (rm 4 1)).trans ((b1o _ (rm 4 0)).trans (ht 4)))))
    ((b4o _ (mne 4 3 (by decide))).trans ((b3o _ (mne 4 2 (by decide))).trans ((b2o _ (mne 4 1 (by decide))).trans
      ((b1o _ (mne 4 0 (by decide))).trans (hm 4)))))
    ((b4o _ (n11 3)).trans ((b3o _ (n11 2)).trans ((b2o _ (n11 1)).trans ((b1o _ (n11 0)).trans hdrv))))
    ((b4o _ (n12 3)).trans ((b3o _ (n12 2)).trans ((b2o _ (n12 1)).trans ((b1o _ (n12 0)).trans hlg))))
  refine ⟨B5, sM.seq (s1.seq (s2.seq (s3.seq (s4.seq s5)))), ?_, ?_, H2t, H2o⟩
  · intro i
    fin_cases i
    · show B5 (Dims.mT pl.ext2 pl.hT 0) = Mw 0
      rw [b5o _ (mne 0 4 (by decide)), b4o _ (mne 0 3 (by decide)), b3o _ (mne 0 2 (by decide)),
        b2o _ (mne 0 1 (by decide)), b1t]
    · show B5 (Dims.mT pl.ext2 pl.hT 1) = Mw 1
      rw [b5o _ (mne 1 4 (by decide)), b4o _ (mne 1 3 (by decide)), b3o _ (mne 1 2 (by decide)), b2t]
    · show B5 (Dims.mT pl.ext2 pl.hT 2) = Mw 2
      rw [b5o _ (mne 2 4 (by decide)), b4o _ (mne 2 3 (by decide)), b3t]
    · show B5 (Dims.mT pl.ext2 pl.hT 3) = Mw 3
      rw [b5o _ (mne 3 4 (by decide)), b4t]
    · exact b5t
  · intro x hx
    rw [b5o _ (fun h => hx 4 h.symm), b4o _ (fun h => hx 3 h.symm), b3o _ (fun h => hx 2 h.symm),
      b2o _ (fun h => hx 1 h.symm), b1o _ (fun h => hx 0 h.symm)]

end Place

/-! ## 4. The exit, in `Inv`'s and the first prologue's terms -/

def KeptM (d : Dims) (eX pX gW X : Nat) (v : Nat) : Prop :=
  Kept d eX pX gW X v ∨ (d.B + 19 + restPc eX pX gW + 5 ≤ v ∧ v < d.B + 19 + restPc eX pX gW + 10)

structure InitOutM {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)
    (L cS cR q b Rc Vv : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool) (H' : Fin T → ℕ) (A' : Fin T → List Bool) :
    Prop where
  drv : A' (d.scr pl.hT 11) = List.replicate Rc true ∧ H' (d.scr pl.hT 11) = 0
  log : A' (d.scr pl.hT 12) = List.replicate (Rc+2) false ∧ H' (d.scr pl.hT 12) = 0
  rew1 : A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = List.replicate Vv true ∧
    H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = 0
  rew2 : A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = List.replicate Vv false ∧
    H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = 0
  /-- `Inv.mU … mv`, `Inv.mH`. -/
  master : ∀ i, A' (Dims.mT pl.ext2 pl.hT i) = masterW L cS cR q b Rc Vv i ∧ H' (Dims.mT pl.ext2 pl.hT i) = 0
  /-- the refresh targets (`InDirt`): the same words, heads 0. -/
  target : ∀ i, A' (Dims.rfT pl.ext2 pl.hT i) = masterW L cS cR q b Rc Vv i ∧ H' (Dims.rfT pl.ext2 pl.hT i) = 0
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
  blank : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → ¬ KeptM d eX pX gW X x.val →
    A' x = List.replicate Rc false ∧ H' x = 0
  junk : ∀ x : Fin T, JB d eX pX gW ≤ x.val → x.val < JB d eX pX gW + X → Rc ≤ (A' x).length ∧ H' x = 0
  below : ∀ x : Fin T, x.val < d.F → (x.val < 278 ∨ 284 ≤ x.val) → A' x = A x ∧ H' x = H x
  low : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 → H' x = 0
  above : ∀ x : Fin T, d.U ≤ x.val → A' x = A x ∧ H' x = H x

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

theorem outM (L cS cR q b Rc Vv : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool) (H1 : Fin T → ℕ)
    (A1 A2 : Fin T → List Bool) (ho : InitOut pl L cS cR q b Rc Vv H A H1 A1)
    (hm2 : ∀ i, A2 (Dims.mT pl.ext2 pl.hT i) = masterW L cS cR q b Rc Vv i)
    (ho2 : ∀ x, (∀ i, Dims.mT pl.ext2 pl.hT i ≠ x) → A2 x = A1 x)
    (ht2 : ∀ i, backH d H1 (Dims.rfT pl.ext2 pl.hT i) = 0)
    (hh2 : ∀ x, (∀ i, Dims.rfT pl.ext2 pl.hT i ≠ x) → backH d H1 x = H1 x) :
    InitOutM pl L cS cR q b Rc Vv H A (backH d H1) A2 := by
  obtain ⟨hF', hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres2 := pl.ext.hjunk
  have hX := pl.ext.hX
  -- off the masters and off the targets, by value
  have oM : ∀ x : Fin T, (x.val < d.B + 19 + restPc eX pX gW + 5 ∨ d.B + 19 + restPc eX pX gW + 10 ≤ x.val) →
      A2 x = A1 x := fun x hx => ho2 x (pl.off_mT x hx)
  have oT : ∀ x : Fin T, (x.val < d.B + 14 ∨ d.B + 18 < x.val) → backH d H1 x = H1 x := by
    intro x hx
    refine hh2 x (fun i h => ?_)
    have hv := congrArg Fin.val h
    rw [pl.rfT_val] at hv
    have := i.isLt
    omega
  have both : ∀ x : Fin T, (x.val < d.B + 14 ∨ (d.B + 18 < x.val ∧ x.val < d.B + 19 + restPc eX pX gW + 5) ∨
      d.B + 19 + restPc eX pX gW + 10 ≤ x.val) → A2 x = A1 x ∧ backH d H1 x = H1 x := by
    intro x hx
    exact ⟨oM x (by omega), oT x (by omega)⟩
  have v11 : (d.scr pl.hT 11).val + 2 = d.B := h11
  have v12 : (d.scr pl.hT 12).val + 1 = d.B := h12
  have vr1 : (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1).val = 278 := rfl
  have vr2 : (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2).val = 279 := rfl
  have vrs : ∀ k : Fin 5, (Dims.rsT pl.ext.rest pl.hT k).val = d.B + 19 + restPc eX pX gW + k.val := fun _ => rfl
  have venc : ∀ k : Fin 13, (Dims.encT (d := d) pl.hT k).val = d.F + d.rt + k.val := fun _ => rfl
  have tr : ∀ x : Fin T, (x.val < d.B + 14 ∨ (d.B + 18 < x.val ∧ x.val < d.B + 19 + restPc eX pX gW + 5) ∨
      d.B + 19 + restPc eX pX gW + 10 ≤ x.val) → ∀ (w : List Bool) (h : ℕ),
      (A1 x = w ∧ H1 x = h) → (A2 x = w ∧ backH d H1 x = h) := by
    intro x hx w h hw
    obtain ⟨e1, e2⟩ := both x hx
    exact ⟨e1.trans hw.1, e2.trans hw.2⟩
  have encx : ∀ k : Fin 13, (Dims.encT (d := d) pl.hT k).val < d.B + 14 := by
    intro k; rw [venc]; have := k.isLt; omega
  have rsx : ∀ k : Fin 5, d.B + 18 < (Dims.rsT pl.ext.rest pl.hT k).val ∧
      (Dims.rsT pl.ext.rest pl.hT k).val < d.B + 19 + restPc eX pX gW + 5 := by
    intro k; rw [vrs]; have := k.isLt; omega
  -- the targets: words kept (off the masters), heads 0
  have tw : ∀ i, A2 (Dims.rfT pl.ext2 pl.hT i) = A1 (Dims.rfT pl.ext2 pl.hT i) := fun i =>
    ho2 _ (fun k h => pl.mT_ne_rfT' k i h)
  have e0 : Dims.rfT pl.ext2 pl.hT 0 = Dims.csSlots pl.ext.rest.ext pl.hT 2 := Fin.ext rfl
  have e1 : Dims.rfT pl.ext2 pl.hT 1 = Dims.drvSlots pl.ext.rest.ext pl.hT 0 := Fin.ext rfl
  have e2 : Dims.rfT pl.ext2 pl.hT 2 = Dims.drvSlots pl.ext.rest.ext pl.hT 1 := Fin.ext rfl
  have e3 : Dims.rfT pl.ext2 pl.hT 3 = Dims.drvSlots pl.ext.rest.ext pl.hT 2 := Fin.ext rfl
  have e4 : Dims.rfT pl.ext2 pl.hT 4 = Dims.drvSlots pl.ext.rest.ext pl.hT 4 := Fin.ext rfl
  refine ⟨tr _ (Or.inl (by omega)) _ _ ho.drv, tr _ (Or.inl (by omega)) _ _ ho.log,
    tr _ (Or.inl (by rw [vr1]; omega)) _ _ ho.rew1, tr _ (Or.inl (by rw [vr2]; omega)) _ _ ho.rew2,
    fun i => ⟨hm2 i, (oT _ (by rw [pl.mT_val]; omega)).trans (ho.blank _ (by rw [pl.mT_val]; omega)
      (by rw [pl.mT_val]; have := i.isLt; omega) (by unfold Kept; rw [pl.mT_val]; have := i.isLt; omega)).2⟩,
    fun i => ⟨?_, ht2 i⟩,
    tr _ (Or.inr (Or.inl (rsx 0))) _ _ ho.big, tr _ (Or.inr (Or.inl (rsx 1))) _ _ ho.small,
    tr _ (Or.inr (Or.inl (rsx 2))) _ _ ho.curT, tr _ (Or.inr (Or.inl (rsx 3))) _ _ ho.wres,
    tr _ (Or.inr (Or.inl (rsx 4))) _ _ ho.qres,
    fun en old => tr _ (Or.inl (encx 3)) _ _ (ho.enc3 en old),
    fun en old => tr _ (Or.inl (encx 6)) _ _ (ho.enc7 en old),
    fun en old => tr _ (Or.inl (encx 7)) _ _ (ho.enc8 en old),
    fun en old => tr _ (Or.inl (encx 8)) _ _ (ho.enc9 en old),
    fun en old => tr _ (Or.inl (encx 9)) _ _ (ho.enc10 en old),
    fun en xs => tr _ (Or.inl (encx 10)) _ _ (ho.app2 en xs),
    fun en xs => tr _ (Or.inl (encx 11)) _ _ (ho.app4 en xs),
    fun en xs => tr _ (Or.inl (encx 12)) _ _ (ho.app5 en xs),
    fun kk hk => tr _ (Or.inl (encx kk)) _ _ (ho.encOld kk hk),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [tw i]
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
  · intro x h1 h2 hk
    have hk' : ¬ Kept d eX pX gW X x.val := fun h => hk (Or.inl h)
    have hkv : ¬ (d.B + 14 ≤ x.val ∧ x.val < d.B + 19) := fun h => hk' (by unfold Kept; omega)
    have hkm : ¬ (d.B + 19 + restPc eX pX gW + 5 ≤ x.val ∧ x.val < d.B + 19 + restPc eX pX gW + 10) :=
      fun h => hk (Or.inr h)
    have hkr : ¬ (d.B + 19 + restPc eX pX gW ≤ x.val ∧ x.val < d.B + 24 + restPc eX pX gW) :=
      fun h => hk' (by unfold Kept; omega)
    exact tr x (by omega) _ _ (ho.blank x h1 h2 hk')
  · intro x h1 h2
    obtain ⟨e1', e2'⟩ := both x (Or.inr (Or.inr (by omega)))
    rw [e1', e2']
    exact ho.junk x h1 h2
  · intro x h1 h2
    exact tr x (Or.inl (by omega)) _ _ (ho.below x h1 h2)
  · intro x h1 h2
    rw [oT x (Or.inl (by omega))]
    exact ho.low x h1 h2
  · intro x h1
    exact tr x (Or.inr (Or.inr (by omega))) _ _ (ho.above x h1)

/-! ## 5. The run -/

end Place

end
end NearCubicWires.SourceConstruction.InitRun
end
