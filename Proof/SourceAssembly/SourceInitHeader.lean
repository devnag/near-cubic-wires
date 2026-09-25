import Proof.SourceAssembly.SourceInitMasters
import Proof.SourceAssembly.SourceFactorSelNat

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
namespace NearCubicWires.SourceConstruction.InitRun
noncomputable section

/-! ## 1. Local stages -/

/-- Docking a zero-head run whose docked tapes are at head 0: the global heads are unchanged. -/
theorem dockZ {t U s n : ℕ} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin t → Fin U) (hi : Function.Injective sl)
    (H : Fin U → ℕ) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0) (hA : ∀ j, A (sl j) = tin j) :
    Step (RecoveryFocus.machine sl p) n H A H (install sl A tout) := by
  have d := h.dock sl hi H A hH hA
  rwa [dockH_existing sl H (fun _ => 0) hH] at d

/-- `poly_step D C`, padded by `Rc` on every tape (input included). -/
theorem polyPad (D C n Rc : ℕ) : ∃ W : Fin (BlockPlatform.UnaryCalc.tapes D) → List Bool,
    Step (PCPSerializerCapacity.Power.machine D C) (PCPSerializerCapacity.Power.budget D C n)
      (fun _ => 0) (fun i => ZeroPadding.pad Rc (if i.val = 0 then List.replicate n true else []))
      (fun _ => 0) W ∧
    W ⟨0, by simp [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes]⟩ =
      ZeroPadding.pad Rc (List.replicate n true) ∧
    W ⟨3+2*D, by simp [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes]⟩ =
      ZeroPadding.pad Rc (List.replicate (C*(n+1)^D) true) ∧
    (∀ j, Rc ≤ (W j).length) := by
  obtain ⟨W, h, h0, h1⟩ := Dimension.stepG D C n
  refine ⟨fun j => ZeroPadding.pad Rc (W j), (h.pad (fun _ => Rc)).congr_in rfl ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [h0]
  · simp only [h1]
  · intro j; exact Uniform.long_pad Rc _

theorem word_local (w : List Bool) (S C : ℕ) (hC : w.length ≤ C) :
    Step (HierarchyFixedWord.machine w) (2 * w.length + 2) (fun _ => 0)
      ![List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad S w, List.replicate C false] := by
  have base := (Step.of_ready (HierarchyFixedWord.word_ready w)).pad ![S, C]
  have hmax : max C w.length = C := by omega
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · exact SourceFactorSel.Desc.pad_nil S
    · exact SourceFactorSel.Desc.pad_nil C
  · funext i
    fin_cases i
    · rfl
    · show ZeroPadding.pad C (List.replicate w.length false) = _
      rw [Rewind.Workspace.pad_zeros, hmax]
      rfl

/-- The fixed-word printer, docked onto `![d, l]`: only `d` changes. -/
theorem word_step {U : ℕ} (w : List Bool) (d l : Fin U) (hdl : d ≠ l) (S C : ℕ) (hC : w.length ≤ C)
    (H : Fin U → ℕ) (A : Fin U → List Bool) (hHd : H d = 0) (hHl : H l = 0)
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (RecoveryFocus.machine (![d, l] : Fin 2 → Fin U) (HierarchyFixedWord.machine w)) (2 * w.length + 2) H A H
      (Function.update A d (ZeroPadding.pad S w)) :=
  SLoad.step_update (word_local w S C hC) 0
    (by
      intro i hi
      fin_cases i
      · exact absurd rfl hi
      · rfl)
    _ (SourceFactorSel.Nat.pair_injective d l hdl) H A
    (by
      intro i
      fin_cases i
      · exact hHd
      · exact hHl)
    (by
      intro i
      fin_cases i
      · exact hd
      · exact hl)

/-! ## 2. The resident block and the header scratch -/

def ZB (d : Dims) (eX pX gW X : Nat) : Nat := JB d eX pX gW + X

/-- The header scratch size for the three cap degrees: template log, the natWord block, three poly blocks. -/
def nsOf (DP DW DL : Nat) : Nat := 23 + (14 + 2*DP) + (14 + 2*DW) + (14 + 2*DL)

/-- The layout fact: room for the init workspace, 32 residents and the header scratch. -/
structure HeadExt (d : Dims) (eX pX gW X NS : Nat) : Prop where
  hres : 64 + restPc eX pX gW + X + NS ≤ d.res

/-- `rsT 4`'s value (the resident `1^q`). -/
abbrev r4V (d : Dims) (eX pX gW : Nat) : Nat := d.B + 19 + restPc eX pX gW + 4

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

include pl in
theorem zlay {NS : Nat} (hh : HeadExt d eX pX gW X NS) :
    ZB d eX pX gW X = d.B + 32 + restPc eX pX gW + X ∧ ZB d eX pX gW X + 32 + NS ≤ d.U ∧ d.U ≤ T ∧
    d.scrV 11 + 2 = d.B ∧ d.scrV 12 + 1 = d.B ∧ JB d eX pX gW = d.B + 32 + restPc eX pX gW := by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have := hh.hres
  exact ⟨by unfold ZB; omega, by unfold ZB; omega, pl.hT, h11, h12, hJB⟩

include pl in
/-- A resident. -/
def zT {NS : Nat} (hh : HeadExt d eX pX gW X NS) (i : Fin 32) : Fin T :=
  ⟨ZB d eX pX gW X + i.val, by
    obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
    have := i.isLt
    omega⟩

theorem zT_val {NS : Nat} (hh : HeadExt d eX pX gW X NS) (i : Fin 32) :
    (pl.zT hh i).val = ZB d eX pX gW X + i.val := rfl

/-! ### The docks, by value -/

def tV (d : Dims) (eX pX gW X : Nat) (j : Nat) : Nat :=
  if j = 0 then r4V d eX pX gW else if j = 1 then ZB d eX pX gW X else ZB d eX pX gW X + 32

include pl in
def tdk {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 1 ≤ NS) : Fin 3 → Fin T := fun j =>
  ⟨tV d eX pX gW X j.val, by
    obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
    unfold tV r4V; split_ifs <;> omega⟩

theorem tdk_inj {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 1 ≤ NS) : Function.Injective (pl.tdk hh hN) := by
  intro a b h
  have hv := congrArg Fin.val h
  obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
  have ha := a.isLt; have hb := b.isLt
  simp only [tdk, tV, r4V] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def pV (d : Dims) (eX pX gW X D o i : Nat) (j : Nat) : Nat :=
  if j = 0 then r4V d eX pX gW else if j = 3 + 2*D then ZB d eX pX gW X + i else ZB d eX pX gW X + 32 + o + j

include pl in
def pdk {NS : Nat} (hh : HeadExt d eX pX gW X NS) (D o i : Nat) (hi : i < 32) (ho : o + (14 + 2*D) ≤ NS) :
    Fin (BlockPlatform.UnaryCalc.tapes D) → Fin T := fun j =>
  ⟨pV d eX pX gW X D o i j.val, by
    obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
    have hj := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at hj
    unfold pV r4V; split_ifs <;> omega⟩

theorem pdk_inj {NS : Nat} (hh : HeadExt d eX pX gW X NS) (D o i : Nat) (hi : i < 32)
    (ho : o + (14 + 2*D) ≤ NS) : Function.Injective (pl.pdk hh D o i hi ho) := by
  intro a b h
  have hv := congrArg Fin.val h
  obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
  have ha := a.isLt; have hb := b.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at ha hb
  simp only [pdk, pV, r4V] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def nV (d : Dims) (eX pX gW X : Nat) (j : Nat) : Nat :=
  if j = 20 then ZB d eX pX gW X + 5 else if j < 22 then ZB d eX pX gW X + 33 + j
  else if j = 22 then r4V d eX pX gW else if j = 23 then d.scrV 11 else d.scrV 12

include pl in
def ndk {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) : Fin 25 → Fin T := fun j =>
  ⟨nV d eX pX gW X j.val, by
    obtain ⟨e1, e2, e3, e4, e5, _⟩ := pl.zlay hh
    have hj := j.isLt
    unfold nV r4V; split_ifs <;> omega⟩

theorem ndk_inj {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) : Function.Injective (pl.ndk hh hN) := by
  intro a b h
  have hv := congrArg Fin.val h
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pl.zlay hh
  have ha := a.isLt; have hb := b.isLt
  simp only [ndk, nV, r4V] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-! ### The machines -/

include pl in
def tmplM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 1 ≤ NS) :=
  RecoveryFocus.machine (pl.tdk hh hN) (DimensionTemplate.machine false)

include pl in
def polyM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (D C o i : Nat) (hi : i < 32) (ho : o + (14 + 2*D) ≤ NS) :=
  RecoveryFocus.machine (pl.pdk hh D o i hi ho) (PCPSerializerCapacity.Power.machine D C)

include pl in
def natSM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) :=
  RecoveryFocus.machine (pl.ndk hh hN) SourceFactorSel.Nat.natM

include pl in
def wordM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (k : Fin 32) (w : List Bool) :=
  RecoveryFocus.machine (![pl.zT hh k, d.scr pl.hT 12] : Fin 2 → Fin T) (HierarchyFixedWord.machine w)

/-! ## 3. Stage runs on the source layout (stated by tape values) -/

theorem r4_eq : (Dims.rsT pl.ext.rest pl.hT 4).val = r4V d eX pX gW := rfl

theorem pad_ones (Rc : ℕ) : ZeroPadding.pad Rc (List.replicate Rc true) = List.replicate Rc true := by
  simp [ZeroPadding.pad]

/-- **Template stage**: `zT 0 := pad Rc (tape q)` from `rsT 4 = pad Rc 1^q`; log on the first scratch tape. -/
theorem tmpl_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 1 ≤ NS) (q Rc : ℕ)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hH : ∀ j, H (pl.tdk hh hN j) = 0)
    (hq : A (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true))
    (hz : ∀ x : Fin T, (x.val = ZB d eX pX gW X ∨ x.val = ZB d eX pX gW X + 32) → A x = List.replicate Rc false) :
    ∃ A', Step (pl.tmplM hh hN) (2*q+8) H A H A' ∧
      (∀ x : Fin T, x.val = ZB d eX pX gW X → A' x = ZeroPadding.pad Rc (UnaryTemplate.tape q)) ∧
      (∀ x : Fin T, x.val = ZB d eX pX gW X + 32 → Rc ≤ (A' x).length) ∧
      (∀ x : Fin T, x.val ≠ ZB d eX pX gW X → x.val ≠ ZB d eX pX gW X + 32 → A' x = A x) := by
  obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
  have st0 := Uniform.stepT false q Rc Rc Rc
  have hin : ∀ j, A (pl.tdk hh hN j) =
      (![ZeroPadding.pad Rc (List.replicate q true), ZeroPadding.pad Rc [], ZeroPadding.pad Rc []] :
        Fin 3 → List Bool) j := by
    intro j
    fin_cases j
    · show A (pl.tdk hh hN 0) = ZeroPadding.pad Rc (List.replicate q true)
      have e : pl.tdk hh hN 0 = Dims.rsT pl.ext.rest pl.hT 4 := Fin.ext (by simp [tdk, tV]; rfl)
      rw [e, hq]
    · show A (pl.tdk hh hN 1) = ZeroPadding.pad Rc []
      rw [SourceFactorSel.Desc.pad_nil]
      exact hz _ (Or.inl (by simp [tdk, tV]))
    · show A (pl.tdk hh hN 2) = ZeroPadding.pad Rc []
      rw [SourceFactorSel.Desc.pad_nil]
      exact hz _ (Or.inr (by simp [tdk, tV]))
  have st := dockZ st0 (pl.tdk hh hN) (pl.tdk_inj hh hN) H A hH hin
  refine ⟨_, st, ?_, ?_, ?_⟩
  · intro x hx
    have e : x = pl.tdk hh hN 1 := Fin.ext (by simp [tdk, tV, hx])
    rw [e, install_slot _ (pl.tdk_inj hh hN)]
    simp
  · intro x hx
    have e : x = pl.tdk hh hN 2 := Fin.ext (by simp [tdk, tV, hx])
    rw [e, install_slot _ (pl.tdk_inj hh hN)]
    exact Uniform.long_pad Rc _
  · intro x h1 h2
    by_cases hx : x = pl.tdk hh hN 0
    · rw [hx, install_slot _ (pl.tdk_inj hh hN)]
      have e : pl.tdk hh hN 0 = Dims.rsT pl.ext.rest pl.hT 4 := Fin.ext (by simp [tdk, tV]; rfl)
      rw [e, hq]; rfl
    · refine install_other _ A _ x (fun j hj => ?_)
      fin_cases j
      · exact hx hj.symm
      · exact h1 (by rw [← hj]; simp [tdk, tV])
      · exact h2 (by rw [← hj]; simp [tdk, tV])

/-- **Cap stage** `(D, C)` at resident `i` with scratch block `[ZB+32+o, ZB+32+o+14+2D)`: `zT i := pad Rc 1^(C(q+1)^D)`. -/
theorem poly_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (D C o i : Nat) (hi : i < 32)
    (ho : o + (14 + 2*D) ≤ NS) (q Rc : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hH : ∀ j, H (pl.pdk hh D o i hi ho j) = 0)
    (hq : A (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true))
    (hz : ∀ x : Fin T, x.val = ZB d eX pX gW X + i → A x = List.replicate Rc false)
    (hs : ∀ x : Fin T, ZB d eX pX gW X + 32 + o ≤ x.val → x.val < ZB d eX pX gW X + 32 + o + (14 + 2*D) →
      A x = List.replicate Rc false) :
    ∃ A', Step (pl.polyM hh D C o i hi ho) (PCPSerializerCapacity.Power.budget D C q) H A H A' ∧
      (∀ x : Fin T, x.val = ZB d eX pX gW X + i → A' x = ZeroPadding.pad Rc (List.replicate (C*(q+1)^D) true)) ∧
      (∀ x : Fin T, ZB d eX pX gW X + 32 + o ≤ x.val → x.val < ZB d eX pX gW X + 32 + o + (14 + 2*D) →
        Rc ≤ (A' x).length) ∧
      (∀ x : Fin T, x.val ≠ ZB d eX pX gW X + i →
        ¬ (ZB d eX pX gW X + 32 + o ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + o + (14 + 2*D)) → A' x = A x) := by
  obtain ⟨W, hW, w0, w1, wl⟩ := polyPad D C q Rc
  obtain ⟨e1, e2, e3, _, _, _⟩ := pl.zlay hh
  have hv : ∀ j : Fin (BlockPlatform.UnaryCalc.tapes D), (pl.pdk hh D o i hi ho j).val =
      pV d eX pX gW X D o i j.val := fun _ => rfl
  have e0 : ∀ j : Fin (BlockPlatform.UnaryCalc.tapes D), j.val = 0 →
      pl.pdk hh D o i hi ho j = Dims.rsT pl.ext.rest pl.hT 4 := by
    intro j h0
    apply Fin.ext
    rw [hv, pl.r4_eq]
    simp [pV, h0]
  have hin : ∀ j, A (pl.pdk hh D o i hi ho j) =
      ZeroPadding.pad Rc (if j.val = 0 then List.replicate q true else []) := by
    intro j
    by_cases h0 : j.val = 0
    · rw [if_pos h0, e0 j h0, hq]
    · rw [if_neg h0, SourceFactorSel.Desc.pad_nil]
      by_cases h3 : j.val = 3 + 2*D
      · exact hz _ (by rw [hv]; simp only [pV, if_neg h0, if_pos h3])
      · have hj' : j.val < 14 + 2*D := j.isLt
        exact hs _ (by rw [hv]; simp only [pV, if_neg h0, if_neg h3]; omega)
          (by rw [hv]; simp only [pV, if_neg h0, if_neg h3]; omega)
  have st := dockZ hW (pl.pdk hh D o i hi ho) (pl.pdk_inj hh D o i hi ho) H A hH hin
  have h3lt : 3 + 2*D < BlockPlatform.UnaryCalc.tapes D := by
    show 3 + 2*D < 14 + 2*D; omega
  refine ⟨_, st, ?_, ?_, ?_⟩
  · intro x hx
    have e : x = pl.pdk hh D o i hi ho ⟨3 + 2*D, h3lt⟩ := Fin.ext (by
      rw [hv]; unfold pV; rw [if_neg (show ¬ (3 + 2*D = 0) by omega), if_pos rfl]; exact hx)
    rw [e, install_slot _ (pl.pdk_inj hh D o i hi ho)]
    exact w1
  · intro x h1 h2
    by_cases hx : ∃ j, pl.pdk hh D o i hi ho j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [install_slot _ (pl.pdk_inj hh D o i hi ho)]
      exact wl j
    · rw [install_other _ A _ x (fun j hj => hx ⟨j, hj⟩), hs x h1 h2]
      simp
  · intro x h1 h2
    by_cases hx : x = Dims.rsT pl.ext.rest pl.hT 4
    · have e : x = pl.pdk hh D o i hi ho ⟨0, by simp [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes]⟩ :=
        hx.trans (e0 _ rfl).symm
      rw [e, install_slot _ (pl.pdk_inj hh D o i hi ho), w0, ← e, hx, hq]
    · refine install_other _ A _ x (fun j hj => ?_)
      have hj' : j.val < 14 + 2*D := j.isLt
      have hxv := congrArg Fin.val hj
      rw [hv] at hxv
      by_cases h0 : j.val = 0
      · exact hx (hj.symm.trans (e0 j h0))
      by_cases h3 : j.val = 3 + 2*D
      · simp only [pV, if_neg h0, if_pos h3] at hxv
        exact h1 hxv.symm
      · simp only [pV, if_neg h0, if_neg h3] at hxv
        exact h2 ⟨by omega, by omega⟩

theorem nat_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) (q Rc : ℕ)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Rc) (hqR : q ≤ Rc)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hH : ∀ j, H (pl.ndk hh hN j) = 0)
    (hq : A (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true))
    (hd : A (d.scr pl.hT 11) = List.replicate Rc true) (hl : A (d.scr pl.hT 12) = List.replicate (Rc+2) false)
    (hz : ∀ x : Fin T, x.val = ZB d eX pX gW X + 5 → A x = List.replicate Rc false)
    (hs : ∀ x : Fin T, ZB d eX pX gW X + 33 ≤ x.val → x.val < ZB d eX pX gW X + 55 → A x = List.replicate Rc false) :
    ∃ A', Step (pl.natSM hh hN) (SourceFactorSel.Nat.natCost q Rc) H A H A' ∧
      (∀ x : Fin T, x.val = ZB d eX pX gW X + 5 → A' x = ZeroPadding.pad Rc (frame (natWord q))) ∧
      (∀ x : Fin T, ZB d eX pX gW X + 33 ≤ x.val → x.val < ZB d eX pX gW X + 55 → Rc ≤ (A' x).length) ∧
      (∀ x : Fin T, x.val ≠ ZB d eX pX gW X + 5 →
        ¬ (ZB d eX pX gW X + 33 ≤ x.val ∧ x.val < ZB d eX pX gW X + 55) → A' x = A x) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pl.zlay hh
  have hv : ∀ j : Fin 25, (pl.ndk hh hN j).val = nV d eX pX gW X j.val := fun _ => rfl
  have e22 : pl.ndk hh hN 22 = Dims.rsT pl.ext.rest pl.hT 4 := Fin.ext (by rw [hv, pl.r4_eq]; simp [nV])
  have e23 : pl.ndk hh hN 23 = d.scr pl.hT 11 := Fin.ext (by rw [hv]; simp [nV]; rfl)
  have e24 : pl.ndk hh hN 24 = d.scr pl.hT 12 := Fin.ext (by rw [hv]; simp [nV]; rfl)
  obtain ⟨A', st, h20, hkeep, hlen, hoff⟩ := SourceFactorSel.Nat.nat_step (pl.ndk hh hN) (pl.ndk_inj hh hN)
    q q Rc Rc Rc (Rc+2) Rc le_rfl hcap hqR le_rfl (by omega) H A hH (by rw [e22, hq])
    (by rw [e23, hd, pad_ones]) (by rw [e24, hl])
    (by
      intro j hj
      by_cases h20 : j.val = 20
      · exact hz _ (by rw [hv]; simp [nV, h20])
      · exact hs _ (by rw [hv]; simp [nV, h20, hj]) (by rw [hv]; simp [nV, h20, hj]; omega))
  refine ⟨A', st, ?_, ?_, ?_⟩
  · intro x hx
    have e : x = pl.ndk hh hN 20 := Fin.ext (by rw [hv]; simp [nV, hx])
    rw [e]; exact h20
  · intro x h1 h2
    by_cases hx : ∃ j, pl.ndk hh hN j = x
    · obtain ⟨j, rfl⟩ := hx
      have hxv := hv j
      have hj' := j.isLt
      by_cases a20 : j.val = 20
      · simp only [nV, if_pos a20] at hxv; omega
      by_cases a22 : j.val < 22
      · exact (hlen j a22).symm ▸ le_rfl
      · have : (pl.ndk hh hN j).val < ZB d eX pX gW X := by
          rw [hxv]; simp only [nV, r4V, if_neg a20, if_neg a22]; split_ifs <;> omega
        omega
    · have e := hoff x (fun j hj => hx ⟨j, hj⟩)
      rw [e, hs x h1 h2]
      simp
  · intro x h1 h2
    by_cases hx : x = Dims.rsT pl.ext.rest pl.hT 4
    · rw [hx, ← e22, hkeep 22 (by decide)]
    by_cases hx23 : x = d.scr pl.hT 11
    · rw [hx23, ← e23, hkeep 23 (by decide)]
    by_cases hx24 : x = d.scr pl.hT 12
    · rw [hx24, ← e24, hkeep 24 (by decide)]
    refine hoff x (fun j hj => ?_)
    have hj' := j.isLt
    have hxv := congrArg Fin.val hj
    rw [hv] at hxv
    by_cases a20 : j.val = 20
    · simp only [nV, if_pos a20] at hxv; exact h1 hxv.symm
    by_cases a22 : j.val < 22
    · simp only [nV, if_neg a20, if_pos a22] at hxv; exact h2 ⟨by omega, by omega⟩
    by_cases a2 : j.val = 22
    · exact hx (hj.symm.trans (by rw [← e22]; exact congrArg _ (Fin.ext a2)))
    by_cases a3 : j.val = 23
    · exact hx23 (hj.symm.trans (by rw [← e23]; exact congrArg _ (Fin.ext a3)))
    · exact hx24 (hj.symm.trans (by rw [← e24]; exact congrArg _ (Fin.ext (by omega))))

/-- **Fixed-word stage** at resident `k` (log `scr 12`). -/
theorem word_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (k : Fin 32) (w : List Bool) (Rc : ℕ)
    (hw : w.length ≤ Rc + 2) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hHk : H (pl.zT hh k) = 0) (hHl : H (d.scr pl.hT 12) = 0)
    (hz : A (pl.zT hh k) = List.replicate Rc false) (hl : A (d.scr pl.hT 12) = List.replicate (Rc+2) false) :
    Step (pl.wordM hh k w) (2 * w.length + 2) H A H (Function.update A (pl.zT hh k) (ZeroPadding.pad Rc w)) := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pl.zlay hh
  have hne : pl.zT hh k ≠ d.scr pl.hT 12 := by
    intro h
    have hv := congrArg Fin.val h
    rw [pl.zT_val] at hv
    have : (d.scr pl.hT 12).val = d.scrV 12 := rfl
    omega
  exact word_step w (pl.zT hh k) (d.scr pl.hT 12) hne Rc (Rc+2) hw H A hHk hHl hz hl

/-! ## 4. The header machine -/

theorem ns_facts {NS DP DW DL : Nat} (hN : nsOf DP DW DL ≤ NS) :
    1 ≤ NS ∧ 23 ≤ NS ∧ 23 + (14 + 2*DP) ≤ NS ∧ 23 + (14 + 2*DP) + (14 + 2*DW) ≤ NS ∧
    23 + (14 + 2*DP) + (14 + 2*DW) + (14 + 2*DL) ≤ NS := by
  unfold nsOf at hN; omega

include pl in
/-- The first quarter: template ; the cap `P`. -/
def headA1M {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW DL : Nat) (hN : nsOf DP DW DL ≤ NS) :=
  Composition.machine (pl.tmplM hh (ns_facts hN).1) (pl.polyM hh DP CP 23 1 (by decide) (ns_facts hN).2.2.1)

include pl in
/-- The second quarter: the caps `W`, `Ld`. -/
def headA2M {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) :=
  Composition.machine (pl.polyM hh DW CW (23 + (14 + 2*DP)) 2 (by decide) (ns_facts hN).2.2.2.1)
    (pl.polyM hh DL CL (23 + (14 + 2*DP) + (14 + 2*DW)) 3 (by decide) (ns_facts hN).2.2.2.2)

include pl in
/-- The first half: template ; the three caps. -/
def headAM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) :=
  Composition.machine (pl.headA1M hh DP CP DW DL hN) (pl.headA2M hh DP DW CW DL CL hN)

include pl in
/-- The second half: tag ; `natWord q` ; `natWord L` ; `natWord target`. -/
def headBM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) (mode : Bool) (L target : Nat) :=
  Composition.machine (pl.wordM hh 4 (SourceFactorSel.Nat.tagWord mode))
  (Composition.machine (pl.natSM hh hN)
  (Composition.machine (pl.wordM hh 6 (frame (natWord L))) (pl.wordM hh 7 (frame (natWord target)))))

include pl in
/-- **The header machine** (ONE fixed machine per `(layout, caps, mode, L, target)`). -/
def headM {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS)
    (mode : Bool) (L target : Nat) :=
  Composition.machine (pl.headAM hh DP CP DW CW DL CL hN) (pl.headBM hh (ns_facts hN).2.1 mode L target)

def costA (DP CP DW CW DL CL q : Nat) : Nat :=
  ((2*q+8) + 1 + PCPSerializerCapacity.Power.budget DP CP q) + 1 +
    (PCPSerializerCapacity.Power.budget DW CW q + 1 + PCPSerializerCapacity.Power.budget DL CL q)

def costB (mode : Bool) (L target q Rc : Nat) : Nat :=
  (2 * (SourceFactorSel.Nat.tagWord mode).length + 2) + 1 + (SourceFactorSel.Nat.natCost q Rc + 1 +
    ((2 * (frame (natWord L)).length + 2) + 1 + (2 * (frame (natWord target)).length + 2)))

/-- Its cost (SMALL: a fixed polynomial in `q`, plus the `O(Rc)` natWord copy). -/
def headCost (DP CP DW CW DL CL : Nat) (mode : Bool) (L target q Rc : Nat) : Nat :=
  costA DP CP DW CW DL CL q + 1 + costB mode L target q Rc

end Place

/-- **The header's exit**: the eight FactorSelection residents on `zT 0..7`, `zT 8..31` still blank, the header scratch
`Rc`-long, everything off the header region unchanged (heads: all unchanged, stated in the `Step`). -/
structure HeadOut {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
    (hh : HeadExt d eX pX gW X NS) (CP CW CL DP DW DL : Nat) (mode : Bool) (L target q Rc : Nat)
    (A A' : Fin T → List Bool) : Prop where
  z0 : A' (pl.zT hh 0) = ZeroPadding.pad Rc (UnaryTemplate.tape q)
  z1 : A' (pl.zT hh 1) = ZeroPadding.pad Rc (List.replicate (CP*(q+1)^DP) true)
  z2 : A' (pl.zT hh 2) = ZeroPadding.pad Rc (List.replicate (CW*(q+1)^DW) true)
  z3 : A' (pl.zT hh 3) = ZeroPadding.pad Rc (List.replicate (CL*(q+1)^DL) true)
  z4 : A' (pl.zT hh 4) = ZeroPadding.pad Rc (SourceFactorSel.Nat.tagWord mode)
  z5 : A' (pl.zT hh 5) = ZeroPadding.pad Rc (frame (natWord q))
  z6 : A' (pl.zT hh 6) = ZeroPadding.pad Rc (frame (natWord L))
  z7 : A' (pl.zT hh 7) = ZeroPadding.pad Rc (frame (natWord target))
  zrest : ∀ i : Fin 32, 8 ≤ i.val → A' (pl.zT hh i) = List.replicate Rc false
  scr : ∀ x : Fin T, ZB d eX pX gW X + 32 ≤ x.val → x.val < ZB d eX pX gW X + 32 + NS → Rc ≤ (A' x).length
  frame : ∀ x : Fin T, ¬ (ZB d eX pX gW X ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS) → A' x = A x

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

/-- First quarter of the header run: template ; cap `P`. -/
theorem headA1_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW DL : Nat) (hN : nsOf DP DW DL ≤ NS)
    (q Rc : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hHv : ∀ x : Fin T, (x.val = r4V d eX pX gW ∨
      (ZB d eX pX gW X ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS)) → H x = 0)
    (hA0 : ∀ x : Fin T, ZB d eX pX gW X ≤ x.val → x.val < ZB d eX pX gW X + 32 + NS →
      A x = List.replicate Rc false)
    (hq : A (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true)) :
    ∃ A2, Step (pl.headA1M hh DP CP DW DL hN) ((2*q+8) + 1 + PCPSerializerCapacity.Power.budget DP CP q) H A H A2 ∧
      A2 (pl.zT hh 0) = ZeroPadding.pad Rc (UnaryTemplate.tape q) ∧
      A2 (pl.zT hh 1) = ZeroPadding.pad Rc (List.replicate (CP*(q+1)^DP) true) ∧
      (∀ x : Fin T, (x.val = ZB d eX pX gW X + 32 ∨
        (ZB d eX pX gW X + 55 ≤ x.val ∧ x.val < ZB d eX pX gW X + 55 + (14 + 2*DP))) → Rc ≤ (A2 x).length) ∧
      (∀ x : Fin T, ¬ (x.val = ZB d eX pX gW X ∨ x.val = ZB d eX pX gW X + 32 ∨ x.val = ZB d eX pX gW X + 1 ∨
        (ZB d eX pX gW X + 55 ≤ x.val ∧ x.val < ZB d eX pX gW X + 55 + (14 + 2*DP))) → A2 x = A x) := by
  obtain ⟨n1, n23, nP, nW, nL⟩ := ns_facts hN
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pl.zlay hh
  have v4 : (Dims.rsT pl.ext.rest pl.hT 4).val = r4V d eX pX gW := rfl
  have hr4 : r4V d eX pX gW = d.B + 19 + restPc eX pX gW + 4 := rfl
  obtain ⟨A1, s1, t1z, t1s, t1f⟩ := pl.tmpl_run hh n1 q Rc H A
    (fun j => hHv _ (by
      have := j.isLt
      simp only [tdk, tV, r4V]
      split_ifs <;> omega)) hq
    (fun x hx => hA0 x (by omega) (by omega))
  obtain ⟨A2, s2, p2z, p2s, p2f⟩ := pl.poly_run hh DP CP 23 1 (by decide) nP q Rc H A1
    (fun j => hHv _ (by
      have hj : j.val < 14 + 2*DP := j.isLt
      simp only [pdk, pV, r4V]
      split_ifs <;> omega))
    ((t1f _ (by omega) (by omega)).trans hq)
    (fun x hx => (t1f x (by omega) (by omega)).trans (hA0 x (by omega) (by omega)))
    (fun x h1 h2 => (t1f x (by omega) (by omega)).trans (hA0 x (by omega) (by omega)))
  have z0v : (pl.zT hh 0).val = ZB d eX pX gW X + 0 := rfl
  have z1v : (pl.zT hh 1).val = ZB d eX pX gW X + 1 := rfl
  refine ⟨A2, s1.seq s2, ?_, p2z _ z1v, ?_, ?_⟩
  · rw [p2f _ (by omega) (by omega)]; exact t1z _ z0v
  · intro x hx
    rcases hx with hx | hx
    · rw [p2f x (by omega) (by omega)]; exact t1s x hx
    · exact p2s x (by omega) (by omega)
  · intro x hx
    exact (p2f x (by omega) (by omega)).trans (t1f x (by omega) (by omega))

/-- Second quarter of the header run: caps `W`, `Ld`. -/
theorem headA2_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS)
    (q Rc : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hHv : ∀ x : Fin T, (x.val = r4V d eX pX gW ∨
      (ZB d eX pX gW X ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS)) → H x = 0)
    (hz : ∀ x : Fin T, (x.val = ZB d eX pX gW X + 2 ∨ x.val = ZB d eX pX gW X + 3 ∨
      (ZB d eX pX gW X + 55 + (14 + 2*DP) ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS)) →
      A x = List.replicate Rc false)
    (hq : A (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true)) :
    ∃ A4, Step (pl.headA2M hh DP DW CW DL CL hN)
      (PCPSerializerCapacity.Power.budget DW CW q + 1 + PCPSerializerCapacity.Power.budget DL CL q) H A H A4 ∧
      A4 (pl.zT hh 2) = ZeroPadding.pad Rc (List.replicate (CW*(q+1)^DW) true) ∧
      A4 (pl.zT hh 3) = ZeroPadding.pad Rc (List.replicate (CL*(q+1)^DL) true) ∧
      (∀ x : Fin T, ZB d eX pX gW X + 55 + (14 + 2*DP) ≤ x.val → x.val < ZB d eX pX gW X + 32 + NS →
        Rc ≤ (A4 x).length) ∧
      (∀ x : Fin T, ¬ (x.val = ZB d eX pX gW X + 2 ∨ x.val = ZB d eX pX gW X + 3 ∨
        (ZB d eX pX gW X + 55 + (14 + 2*DP) ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS)) → A4 x = A x) := by
  obtain ⟨n1, n23, nP, nW, nL⟩ := ns_facts hN
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pl.zlay hh
  have v4 : (Dims.rsT pl.ext.rest pl.hT 4).val = r4V d eX pX gW := rfl
  have hr4 : r4V d eX pX gW = d.B + 19 + restPc eX pX gW + 4 := rfl
  obtain ⟨A3, s3, p3z, p3s, p3f⟩ := pl.poly_run hh DW CW (23 + (14 + 2*DP)) 2 (by decide) nW q Rc H A
    (fun j => hHv _ (by
      have hj : j.val < 14 + 2*DW := j.isLt
      simp only [pdk, pV, r4V]
      split_ifs <;> omega)) hq
    (fun x hx => hz x (by omega))
    (fun x h1 h2 => hz x (by omega))
  obtain ⟨A4, s4, p4z, p4s, p4f⟩ := pl.poly_run hh DL CL (23 + (14 + 2*DP) + (14 + 2*DW)) 3 (by decide) nL q Rc
    H A3
    (fun j => hHv _ (by
      have hj : j.val < 14 + 2*DL := j.isLt
      simp only [pdk, pV, r4V]
      split_ifs <;> omega))
    ((p3f _ (by omega) (by omega)).trans hq)
    (fun x hx => (p3f x (by omega) (by omega)).trans (hz x (by omega)))
    (fun x h1 h2 => (p3f x (by omega) (by omega)).trans (hz x (by omega)))
  have z2v : (pl.zT hh 2).val = ZB d eX pX gW X + 2 := rfl
  have z3v : (pl.zT hh 3).val = ZB d eX pX gW X + 3 := rfl
  refine ⟨A4, s3.seq s4, ?_, p4z _ z3v, ?_, ?_⟩
  · rw [p4f _ (by omega) (by omega)]; exact p3z _ z2v
  · intro x h1 h2
    by_cases c3 : x.val < ZB d eX pX gW X + 32 + (23 + (14 + 2*DP)) + (14 + 2*DW)
    · rw [p4f x (by omega) (by omega)]; exact p3s x (by omega) c3
    by_cases c4 : x.val < ZB d eX pX gW X + 32 + (23 + (14 + 2*DP) + (14 + 2*DW)) + (14 + 2*DL)
    · exact p4s x (by omega) c4
    · rw [p4f x (by omega) (by omega), p3f x (by omega) (by omega), hz x (by omega)]
      simp
  · intro x hx
    exact (p4f x (by omega) (by omega)).trans (p3f x (by omega) (by omega))

/-- **First half of the header run** (template ; caps `P W Ld`). -/
theorem headA_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS)
    (q Rc : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hHv : ∀ x : Fin T, (x.val = r4V d eX pX gW ∨
      (ZB d eX pX gW X ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS)) → H x = 0)
    (hA0 : ∀ x : Fin T, ZB d eX pX gW X ≤ x.val → x.val < ZB d eX pX gW X + 32 + NS →
      A x = List.replicate Rc false)
    (hq : A (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true)) :
    ∃ A4, Step (pl.headAM hh DP CP DW CW DL CL hN) (costA DP CP DW CW DL CL q) H A H A4 ∧
      A4 (pl.zT hh 0) = ZeroPadding.pad Rc (UnaryTemplate.tape q) ∧
      A4 (pl.zT hh 1) = ZeroPadding.pad Rc (List.replicate (CP*(q+1)^DP) true) ∧
      A4 (pl.zT hh 2) = ZeroPadding.pad Rc (List.replicate (CW*(q+1)^DW) true) ∧
      A4 (pl.zT hh 3) = ZeroPadding.pad Rc (List.replicate (CL*(q+1)^DL) true) ∧
      (∀ x : Fin T, ZB d eX pX gW X + 32 ≤ x.val → x.val < ZB d eX pX gW X + 32 + NS →
        ¬ (ZB d eX pX gW X + 33 ≤ x.val ∧ x.val < ZB d eX pX gW X + 55) → Rc ≤ (A4 x).length) ∧
      (∀ x : Fin T, ¬ (x.val = ZB d eX pX gW X ∨ x.val = ZB d eX pX gW X + 32 ∨
        (ZB d eX pX gW X + 1 ≤ x.val ∧ x.val ≤ ZB d eX pX gW X + 3) ∨
        (ZB d eX pX gW X + 55 ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS)) → A4 x = A x) := by
  obtain ⟨n1, n23, nP, nW, nL⟩ := ns_facts hN
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pl.zlay hh
  have v4 : (Dims.rsT pl.ext.rest pl.hT 4).val = r4V d eX pX gW := rfl
  have hr4 : r4V d eX pX gW = d.B + 19 + restPc eX pX gW + 4 := rfl
  obtain ⟨A2, s2, a0, a1, aS, aF⟩ := pl.headA1_run hh DP CP DW DL hN q Rc H A hHv hA0 hq
  obtain ⟨A4, s4, b2, b3, bS, bF⟩ := pl.headA2_run hh DP DW CW DL CL hN q Rc H A2 hHv
    (fun x hx => (aF x (by omega)).trans (hA0 x (by omega) (by omega)))
    ((aF _ (by omega)).trans hq)
  have z0v : (pl.zT hh 0).val = ZB d eX pX gW X + 0 := rfl
  have z1v : (pl.zT hh 1).val = ZB d eX pX gW X + 1 := rfl
  refine ⟨A4, s2.seq s4, ?_, ?_, b2, b3, ?_, ?_⟩
  · rw [bF _ (by omega)]; exact a0
  · rw [bF _ (by omega)]; exact a1
  · intro x h1 h2 h3
    by_cases c : ZB d eX pX gW X + 55 + (14 + 2*DP) ≤ x.val
    · exact bS x c h2
    · rw [bF x (by omega)]
      by_cases c1 : x.val = ZB d eX pX gW X + 32 ∨
          (ZB d eX pX gW X + 55 ≤ x.val ∧ x.val < ZB d eX pX gW X + 55 + (14 + 2*DP))
      · exact aS x c1
      · rw [aF x (by omega), hA0 x (by omega) h2]
        simp
  · intro x hx
    exact (bF x (by omega)).trans (aF x (by omega))

/-- **Second half of the header run** (tag ; `natWord q` ; `natWord L` ; `natWord target`). -/
theorem headB_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (hN : 23 ≤ NS) (mode : Bool) (L target q Rc : ℕ)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Rc) (hqR : q ≤ Rc)
    (hLw : (frame (natWord L)).length ≤ Rc + 2) (hTw : (frame (natWord target)).length ≤ Rc + 2)
    (h5 : 5 ≤ Rc) (H : Fin T → ℕ) (B : Fin T → List Bool)
    (hHv : ∀ x : Fin T, (x.val = r4V d eX pX gW ∨ x.val = d.scrV 11 ∨ x.val = d.scrV 12 ∨
      (ZB d eX pX gW X ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS)) → H x = 0)
    (hq : B (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true))
    (hd : B (d.scr pl.hT 11) = List.replicate Rc true) (hl : B (d.scr pl.hT 12) = List.replicate (Rc+2) false)
    (hz : ∀ x : Fin T, ZB d eX pX gW X + 4 ≤ x.val → x.val ≤ ZB d eX pX gW X + 7 → B x = List.replicate Rc false)
    (hs : ∀ x : Fin T, ZB d eX pX gW X + 33 ≤ x.val → x.val < ZB d eX pX gW X + 55 → B x = List.replicate Rc false) :
    ∃ B', Step (pl.headBM hh hN mode L target) (costB mode L target q Rc) H B H B' ∧
      B' (pl.zT hh 4) = ZeroPadding.pad Rc (SourceFactorSel.Nat.tagWord mode) ∧
      B' (pl.zT hh 5) = ZeroPadding.pad Rc (frame (natWord q)) ∧
      B' (pl.zT hh 6) = ZeroPadding.pad Rc (frame (natWord L)) ∧
      B' (pl.zT hh 7) = ZeroPadding.pad Rc (frame (natWord target)) ∧
      (∀ x : Fin T, ZB d eX pX gW X + 33 ≤ x.val → x.val < ZB d eX pX gW X + 55 → Rc ≤ (B' x).length) ∧
      (∀ x : Fin T, ¬ (ZB d eX pX gW X + 4 ≤ x.val ∧ x.val ≤ ZB d eX pX gW X + 7) →
        ¬ (ZB d eX pX gW X + 33 ≤ x.val ∧ x.val < ZB d eX pX gW X + 55) → B' x = B x) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pl.zlay hh
  have v4 : (Dims.rsT pl.ext.rest pl.hT 4).val = r4V d eX pX gW := rfl
  have v11 : (d.scr pl.hT 11).val = d.scrV 11 := rfl
  have v12 : (d.scr pl.hT 12).val = d.scrV 12 := rfl
  have hr4 : r4V d eX pX gW = d.B + 19 + restPc eX pX gW + 4 := rfl
  have z4v : (pl.zT hh 4).val = ZB d eX pX gW X + 4 := rfl
  have z5v : (pl.zT hh 5).val = ZB d eX pX gW X + 5 := rfl
  have z6v : (pl.zT hh 6).val = ZB d eX pX gW X + 6 := rfl
  have z7v : (pl.zT hh 7).val = ZB d eX pX gW X + 7 := rfl
  have hz4 := hz (pl.zT hh 4) (by omega) (by omega)
  have s5 := pl.word_run hh 4 (SourceFactorSel.Nat.tagWord mode) Rc
    (by rw [SourceFactorSel.Nat.tagWord_length]; omega) H B (hHv _ (by omega))
    (hHv _ (by omega)) hz4 hl
  set B5 := Function.update B (pl.zT hh 4) (ZeroPadding.pad Rc (SourceFactorSel.Nat.tagWord mode)) with hB5
  have g5 : ∀ x : Fin T, x.val ≠ ZB d eX pX gW X + 4 → B5 x = B x := fun x hx =>
    Function.update_of_ne (fun h => hx (by rw [h, z4v])) _ _
  obtain ⟨B6, s6, n6z, n6s, n6f⟩ := pl.nat_run hh hN q Rc hcap hqR H B5
    (fun j => hHv _ (by
      have := j.isLt
      simp only [ndk, nV, r4V]
      split_ifs <;> omega))
    ((g5 _ (by omega)).trans hq) ((g5 _ (by omega)).trans hd)
    ((g5 _ (by omega)).trans hl)
    (fun x hx => (g5 x (by omega)).trans (hz x (by omega) (by omega)))
    (fun x h1 h2 => (g5 x (by omega)).trans (hs x h1 h2))
  have u6 : ∀ x : Fin T, ¬ (ZB d eX pX gW X + 4 ≤ x.val ∧ x.val ≤ ZB d eX pX gW X + 5) →
      ¬ (ZB d eX pX gW X + 33 ≤ x.val ∧ x.val < ZB d eX pX gW X + 55) → B6 x = B x :=
    fun x h1 h2 => (n6f x (by omega) h2).trans (g5 x (by omega))
  have s7 := pl.word_run hh 6 (frame (natWord L)) Rc hLw H B6 (hHv _ (by omega))
    (hHv _ (by omega))
    ((u6 _ (by omega) (by omega)).trans (hz _ (by omega) (by omega)))
    ((u6 _ (by omega) (by omega)).trans hl)
  set B7 := Function.update B6 (pl.zT hh 6) (ZeroPadding.pad Rc (frame (natWord L))) with hB7
  have g7 : ∀ x : Fin T, x.val ≠ ZB d eX pX gW X + 6 → B7 x = B6 x := fun x hx =>
    Function.update_of_ne (fun h => hx (by rw [h, z6v])) _ _
  have s8 := pl.word_run hh 7 (frame (natWord target)) Rc hTw H B7 (hHv _ (by omega))
    (hHv _ (by omega))
    ((g7 _ (by omega)).trans ((u6 _ (by omega) (by omega)).trans
      (hz _ (by omega) (by omega))))
    ((g7 _ (by omega)).trans ((u6 _ (by omega) (by omega)).trans hl))
  set B8 := Function.update B7 (pl.zT hh 7) (ZeroPadding.pad Rc (frame (natWord target))) with hB8
  have g8 : ∀ x : Fin T, x.val ≠ ZB d eX pX gW X + 7 → B8 x = B7 x := fun x hx =>
    Function.update_of_ne (fun h => hx (by rw [h, z7v])) _ _
  refine ⟨B8, s5.seq (s6.seq (s7.seq s8)), ?_, ?_, ?_, Function.update_self _ _ _, ?_, ?_⟩
  · rw [g8 _ (by omega), g7 _ (by omega), n6f _ (by omega) (by omega)]
    exact Function.update_self _ _ _
  · rw [g8 _ (by omega), g7 _ (by omega)]
    exact n6z _ z5v
  · rw [g8 _ (by omega)]
    exact Function.update_self _ _ _
  · intro x h1 h2
    rw [g8 x (by omega), g7 x (by omega)]
    exact n6s x h1 h2
  · intro x h1 h2
    rw [g8 x (by omega), g7 x (by omega)]
    exact u6 x (by omega) h2

/-- **The header run.** From blank resident/scratch tapes (heads 0), the resident `1^q` on `rsT 4` and the clear
driver/log: ONE fixed machine writes the eight FactorSelection residents; no head moves. -/
theorem head_run {NS : Nat} (hh : HeadExt d eX pX gW X NS) (DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS)
    (mode : Bool) (L target q Rc : ℕ)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Rc) (hqR : q ≤ Rc)
    (hLw : (frame (natWord L)).length ≤ Rc + 2) (hTw : (frame (natWord target)).length ≤ Rc + 2)
    (h5 : 5 ≤ Rc) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hreg : ∀ x : Fin T, ZB d eX pX gW X ≤ x.val → x.val < ZB d eX pX gW X + 32 + NS →
      A x = List.replicate Rc false ∧ H x = 0)
    (hq : A (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true))
    (hqH : H (Dims.rsT pl.ext.rest pl.hT 4) = 0)
    (hd : A (d.scr pl.hT 11) = List.replicate Rc true) (hdH : H (d.scr pl.hT 11) = 0)
    (hl : A (d.scr pl.hT 12) = List.replicate (Rc+2) false) (hlH : H (d.scr pl.hT 12) = 0) :
    ∃ A', Step (pl.headM hh DP CP DW CW DL CL hN mode L target) (headCost DP CP DW CW DL CL mode L target q Rc)
      H A H A' ∧ HeadOut pl hh CP CW CL DP DW DL mode L target q Rc A A' := by
  obtain ⟨n1, n23, nP, nW, nL⟩ := ns_facts hN
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := pl.zlay hh
  have v4 : (Dims.rsT pl.ext.rest pl.hT 4).val = r4V d eX pX gW := rfl
  have v11 : (d.scr pl.hT 11).val = d.scrV 11 := rfl
  have v12 : (d.scr pl.hT 12).val = d.scrV 12 := rfl
  have hr4 : r4V d eX pX gW = d.B + 19 + restPc eX pX gW + 4 := rfl
  have vz : ∀ i : Fin 32, (pl.zT hh i).val = ZB d eX pX gW X + i.val := fun _ => rfl
  have hHv : ∀ x : Fin T, (x.val = r4V d eX pX gW ∨ x.val = d.scrV 11 ∨ x.val = d.scrV 12 ∨
      (ZB d eX pX gW X ≤ x.val ∧ x.val < ZB d eX pX gW X + 32 + NS)) → H x = 0 := by
    intro x hx
    rcases hx with h | h | h | h
    · rw [show x = Dims.rsT pl.ext.rest pl.hT 4 from Fin.ext h]; exact hqH
    · rw [show x = d.scr pl.hT 11 from Fin.ext h]; exact hdH
    · rw [show x = d.scr pl.hT 12 from Fin.ext h]; exact hlH
    · exact (hreg x h.1 h.2).2
  have hA0 : ∀ x : Fin T, ZB d eX pX gW X ≤ x.val → x.val < ZB d eX pX gW X + 32 + NS →
      A x = List.replicate Rc false := fun x h1 h2 => (hreg x h1 h2).1
  obtain ⟨A4, sA, a0, a1, a2, a3, aS, aF⟩ := pl.headA_run hh DP CP DW CW DL CL hN q Rc H A
    (fun x hx => hHv x (by omega)) hA0 hq
  obtain ⟨A8, sB, b4, b5, b6, b7, bS, bF⟩ := pl.headB_run hh n23 mode L target q Rc hcap hqR hLw hTw h5 H A4 hHv
    ((aF _ (by omega)).trans hq) ((aF _ (by omega)).trans hd)
    ((aF _ (by omega)).trans hl)
    (fun x h1 h2 => (aF x (by omega)).trans (hA0 x (by omega) (by omega)))
    (fun x h1 h2 => (aF x (by omega)).trans (hA0 x (by omega) (by omega)))
  have z0v : (pl.zT hh 0).val = ZB d eX pX gW X + 0 := rfl
  have z1v : (pl.zT hh 1).val = ZB d eX pX gW X + 1 := rfl
  have z2v : (pl.zT hh 2).val = ZB d eX pX gW X + 2 := rfl
  have z3v : (pl.zT hh 3).val = ZB d eX pX gW X + 3 := rfl
  refine ⟨A8, sA.seq sB, ⟨?_, ?_, ?_, ?_, b4, b5, b6, b7, ?_, ?_, ?_⟩⟩
  · rw [bF _ (by omega) (by omega)]; exact a0
  · rw [bF _ (by omega) (by omega)]; exact a1
  · rw [bF _ (by omega) (by omega)]; exact a2
  · rw [bF _ (by omega) (by omega)]; exact a3
  · intro i hi
    have hi2 := i.isLt
    rw [bF _ (by rw [vz]; omega) (by rw [vz]; omega), aF _ (by rw [vz]; omega)]
    exact hA0 _ (by rw [vz]; omega) (by rw [vz]; omega)
  · intro x h1 h2
    by_cases c : ZB d eX pX gW X + 33 ≤ x.val ∧ x.val < ZB d eX pX gW X + 55
    · exact bS x c.1 c.2
    · rw [bF x (by omega) c]; exact aS x h1 h2 c
  · intro x hx
    rw [bF x (by omega) (by omega), aF x (by omega)]

end Place

end
end NearCubicWires.SourceConstruction.InitRun
end
