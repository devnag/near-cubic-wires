import Proof.SourceAssembly.SourceSkelInitS

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

/-- The extension scratch base: right after SI's header scratch. -/
abbrev eb (d : Dims) (eX pX gW X NS : Nat) : Nat := d.B + 64 + restPc eX pX gW + X + NS

/-- The layout fact for the extension scratch of size `NE`. -/
structure ResExt (d : Dims) (eX pX gW X NS NE : Nat) : Prop where
  hres : 64 + restPc eX pX gW + X + NS + NE ≤ d.res

/-- A strip slot's content: a written resident, or blank at `Rc`. -/
def slotVal (Rc : Nat) (val : Nat → Option (List Bool)) (i : Nat) : List Bool :=
  match val i with
  | some w => w
  | none => List.replicate Rc false

theorem slotVal_none (Rc : Nat) (val : Nat → Option (List Bool)) (i : Nat) (h : val i = none) :
    slotVal Rc val i = List.replicate Rc false := by
  unfold slotVal; rw [h]

theorem slotVal_some (Rc : Nat) (val : Nat → Option (List Bool)) (i : Nat) (w : List Bool) (h : val i = some w) :
    slotVal Rc val i = w := by
  unfold slotVal; rw [h]

/-! ## 1. Generic docked stages on the universe (by tape value) -/

section docks
variable {T : Nat}

/-- The polynomial run's dock: input `inp`, output `out`, workspace `e + j`. -/
def polyDkV (inp out e D : Nat) (j : Nat) : Nat :=
  if j = 0 then inp else if j = 3 + 2*D then out else e + j

/-- The dock (block `[e, e+14+2D)`). -/
def polyDk (inp out : Fin T) (e D : Nat) (h : e + 14 + 2*D ≤ T) : Fin (BlockPlatform.UnaryCalc.tapes D) → Fin T :=
  fun j => ⟨polyDkV inp.val out.val e D j.val, by
    have hj := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at hj
    unfold polyDkV; split_ifs
    · exact inp.isLt
    · exact out.isLt
    · omega⟩

theorem polyDk_inj (inp out : Fin T) (e D : Nat) (h : e + 14 + 2*D ≤ T) (hio : inp.val ≠ out.val)
    (hi : inp.val < e ∨ e + 14 + 2*D ≤ inp.val) (ho : out.val < e ∨ e + 14 + 2*D ≤ out.val) :
    Function.Injective (polyDk inp out e D h) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt; have hb := b.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at ha hb
  simp only [polyDk, polyDkV] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The polynomial stage `C·(n+1)^D` from `inp` onto `out`. -/
def polyAtM (inp out : Fin T) (e D C : Nat) (h : e + 14 + 2*D ≤ T) :=
  RecoveryFocus.machine (polyDk inp out e D h) (PCPSerializerCapacity.Power.machine D C)

/-- **Polynomial stage, by value.** Input `pad Rc 1^n` on `inp`, blank `out` and workspace (`0^Rc`, heads 0): `out` gets
`pad Rc 1^(C(n+1)^D)`, the workspace is `Rc`-long, nothing else changes, no head moves. -/
theorem polyAt_run (D C n Rc : Nat) (inp out : Fin T) (e : Nat) (h : e + 14 + 2*D ≤ T) (hio : inp.val ≠ out.val)
    (hi : inp.val < e ∨ e + 14 + 2*D ≤ inp.val) (ho : out.val < e ∨ e + 14 + 2*D ≤ out.val)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hHi : H inp = 0) (hHo : H out = 0)
    (hHs : ∀ x : Fin T, e ≤ x.val → x.val < e + 14 + 2*D → H x = 0)
    (hin : A inp = ZeroPadding.pad Rc (List.replicate n true)) (hz : A out = List.replicate Rc false)
    (hs : ∀ x : Fin T, e ≤ x.val → x.val < e + 14 + 2*D → A x = List.replicate Rc false) :
    ∃ A', Step (polyAtM inp out e D C h) (PCPSerializerCapacity.Power.budget D C n) H A H A' ∧
      A' out = ZeroPadding.pad Rc (List.replicate (C*(n+1)^D) true) ∧
      (∀ x : Fin T, e ≤ x.val → x.val < e + 14 + 2*D → Rc ≤ (A' x).length) ∧
      (∀ x : Fin T, x ≠ out → ¬ (e ≤ x.val ∧ x.val < e + 14 + 2*D) → A' x = A x) := by
  obtain ⟨W, hW, w0, w1, wl⟩ := polyPad D C n Rc
  have hinj := polyDk_inj inp out e D h hio hi ho
  have hv : ∀ j : Fin (BlockPlatform.UnaryCalc.tapes D), (polyDk inp out e D h j).val =
      polyDkV inp.val out.val e D j.val := fun _ => rfl
  have e0 : ∀ j : Fin (BlockPlatform.UnaryCalc.tapes D), j.val = 0 → polyDk inp out e D h j = inp := by
    intro j h0
    apply Fin.ext
    rw [hv]; simp [polyDkV, h0]
  have e3 : ∀ j : Fin (BlockPlatform.UnaryCalc.tapes D), j.val = 3 + 2*D → polyDk inp out e D h j = out := by
    intro j h3
    apply Fin.ext
    rw [hv]; unfold polyDkV; rw [if_neg (by omega), if_pos h3]
  have hH : ∀ j, H (polyDk inp out e D h j) = 0 := by
    intro j
    by_cases h0 : j.val = 0
    · rw [e0 j h0]; exact hHi
    by_cases h3 : j.val = 3 + 2*D
    · rw [e3 j h3]; exact hHo
    have hj := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at hj
    exact hHs _ (by rw [hv]; simp only [polyDkV, if_neg h0, if_neg h3]; omega)
      (by rw [hv]; simp only [polyDkV, if_neg h0, if_neg h3]; omega)
  have hin' : ∀ j, A (polyDk inp out e D h j) =
      ZeroPadding.pad Rc (if j.val = 0 then List.replicate n true else []) := by
    intro j
    by_cases h0 : j.val = 0
    · rw [if_pos h0, e0 j h0, hin]
    · rw [if_neg h0, SourceFactorSel.Desc.pad_nil]
      by_cases h3 : j.val = 3 + 2*D
      · rw [e3 j h3]; exact hz
      · have hj := j.isLt
        simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at hj
        exact hs _ (by rw [hv]; simp only [polyDkV, if_neg h0, if_neg h3]; omega)
          (by rw [hv]; simp only [polyDkV, if_neg h0, if_neg h3]; omega)
  have st := dockZ hW (polyDk inp out e D h) hinj H A hH hin'
  have h3lt : 3 + 2*D < BlockPlatform.UnaryCalc.tapes D := by
    show 3 + 2*D < 14 + 2*D; omega
  refine ⟨_, st, ?_, ?_, ?_⟩
  · have hs3 := install_slot (polyDk inp out e D h) hinj A W ⟨3 + 2*D, h3lt⟩
    rw [e3 _ rfl] at hs3
    rw [hs3]
    exact w1
  · intro x h1 h2
    by_cases hx : ∃ j, polyDk inp out e D h j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [install_slot _ hinj]
      exact wl j
    · rw [install_other _ A _ x (fun j hj => hx ⟨j, hj⟩), hs x h1 h2]
      simp
  · intro x h1 h2
    by_cases hx : x = inp
    · have e' : x = polyDk inp out e D h ⟨0, by simp [DimensionPolynomial.tapes]⟩ :=
        hx.trans (e0 _ rfl).symm
      rw [e', install_slot _ hinj, w0, ← e', hx, hin]
    · refine install_other _ A _ x (fun j hj => ?_)
      have hj' := j.isLt
      simp only [DimensionPolynomial.tapes] at hj'
      by_cases h0 : j.val = 0
      · exact hx (hj.symm.trans (e0 j h0))
      by_cases h3 : j.val = 3 + 2*D
      · exact h1 (hj.symm.trans (e3 j h3))
      · have hxv := congrArg Fin.val hj
        rw [hv] at hxv
        simp only [polyDkV, if_neg h0, if_neg h3] at hxv
        exact h2 ⟨by omega, by omega⟩

/-- The copier's dock. -/
def copyAtM (src b0 drv log : Fin T) :=
  RecoveryFocus.machine (![src, b0, drv, log] : Fin 4 → Fin T) ClockUnarySum.machine

theorem quad_injective (a b c e : Fin T) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hae : a.val ≠ e.val)
    (hbc : b.val ≠ c.val) (hbe : b.val ≠ e.val) (hce : c.val ≠ e.val) :
    Function.Injective (![a, b, c, e] : Fin 4 → Fin T) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> simp at hv <;> first | rfl | omega

/-- **Copier stage, padded.** `src = 1^r` with `Rc ≤ r`, blank `b0, drv, log` (`0^Rc`, heads 0): `drv := 1^r`, `log := 0^(r+2)`
EXACTLY; `src`, `b0` and everything else unchanged; no head moves. -/
theorem copyAt_run (r Rc : Nat) (hr : Rc ≤ r) (src b0 drv log : Fin T) (hab : src.val ≠ b0.val)
    (hac : src.val ≠ drv.val) (hae : src.val ≠ log.val) (hbc : b0.val ≠ drv.val) (hbe : b0.val ≠ log.val)
    (hce : drv.val ≠ log.val) (H : Fin T → ℕ) (A : Fin T → List Bool)
    (hH1 : H src = 0) (hH2 : H b0 = 0) (hH3 : H drv = 0) (hH4 : H log = 0)
    (hA1 : A src = List.replicate r true) (hA2 : A b0 = List.replicate Rc false)
    (hA3 : A drv = List.replicate Rc false) (hA4 : A log = List.replicate Rc false) :
    ∃ A', Step (copyAtM src b0 drv log) (2*r+6) H A H A' ∧
      A' drv = List.replicate r true ∧ A' log = List.replicate (r+2) false ∧
      (∀ x : Fin T, x ≠ drv → x ≠ log → A' x = A x) := by
  have hinj := quad_injective src b0 drv log hab hac hae hbc hbe hce
  have base := (BlockPlatform.UnaryCalc.copy_step r).pad (fun _ => Rc)
  have p1 : ZeroPadding.pad Rc (List.replicate r true) = List.replicate r true := by
    simp [ZeroPadding.pad, Nat.sub_eq_zero_of_le hr]
  have p2 : ZeroPadding.pad Rc (List.replicate (r+2) false) = List.replicate (r+2) false := by
    simp [ZeroPadding.pad, Nat.sub_eq_zero_of_le (show Rc ≤ r + 2 by omega)]
  have hin : (fun i => ZeroPadding.pad ((fun _ : Fin 4 => Rc) i)
      ((![List.replicate r true, [], [], []] : Fin 4 → List Bool) i)) =
      ![List.replicate r true, List.replicate Rc false, List.replicate Rc false, List.replicate Rc false] := by
    funext i
    fin_cases i
    · exact p1
    · exact SourceFactorSel.Desc.pad_nil Rc
    · exact SourceFactorSel.Desc.pad_nil Rc
    · exact SourceFactorSel.Desc.pad_nil Rc
  have hout : (fun i => ZeroPadding.pad ((fun _ : Fin 4 => Rc) i)
      ((![List.replicate r true, [], List.replicate r true, List.replicate (r+2) false] : Fin 4 → List Bool) i)) =
      ![List.replicate r true, List.replicate Rc false, List.replicate r true, List.replicate (r+2) false] := by
    funext i
    fin_cases i
    · exact p1
    · exact SourceFactorSel.Desc.pad_nil Rc
    · exact p1
    · exact p2
  have st0 := (base.congr_in rfl hin).congr rfl hout
  have st := dockZ st0 (![src, b0, drv, log] : Fin 4 → Fin T) hinj H A
    (by intro j; fin_cases j <;> assumption)
    (by intro j; fin_cases j <;> assumption)
  refine ⟨_, st, ?_, ?_, ?_⟩
  · exact install_slot _ hinj A _ (2 : Fin 4)
  · exact install_slot _ hinj A _ (3 : Fin 4)
  · intro x h3 h4
    by_cases e1 : x = src
    · rw [e1]; exact (install_slot _ hinj A _ (0 : Fin 4)).trans hA1.symm
    by_cases e2 : x = b0
    · rw [e2]; exact (install_slot _ hinj A _ (1 : Fin 4)).trans hA2.symm
    refine install_other _ A _ x (fun j hj => ?_)
    fin_cases j
    · exact e1 hj.symm
    · exact e2 hj.symm
    · exact h3 hj.symm
    · exact h4 hj.symm

end docks

/-! ## 2. The invariant over the strip and the extension scratch -/

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-- **The init's running exit** after `initS` and any number of resident stages. -/
structure InitInv (NR NE : Nat) (L cS cR q b Rc Vv CP CW CL DP DW DL : Nat) (mode : Bool) (tg : Nat)
    (val : Nat → Option (List Bool)) (u : Nat)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (H' : Fin T → ℕ) (A' : Fin T → List Bool) : Prop where
  /-- Off the written strip and the extension scratch, the bank is `InitOutS`'s. -/
  base : ∃ (H1 : Fin T → ℕ) (A1 : Fin T → List Bool),
    InitOutS pl hh NR L cS cR q b Rc Vv CP CW CL DP DW DL mode tg H A H1 A1 ∧
    ∀ x : Fin T, ¬ (sb d eX pX gW + 8 ≤ x.val ∧ x.val < sb d eX pX gW + NR) →
      ¬ (eb d eX pX gW X NS ≤ x.val ∧ x.val < eb d eX pX gW X NS + NE) → A' x = A1 x ∧ H' x = H1 x
  /-- The strip slots `8 .. NR-1`: their residents (or blank), heads 0. -/
  strip : ∀ x : Fin T, sb d eX pX gW + 8 ≤ x.val → x.val < sb d eX pX gW + NR →
    A' x = slotVal Rc val (x.val - sb d eX pX gW) ∧ H' x = 0
  /-- The used extension scratch. -/
  used : ∀ x : Fin T, eb d eX pX gW X NS ≤ x.val → x.val < eb d eX pX gW X NS + u → Rc ≤ (A' x).length ∧ H' x = 0
  /-- The fresh extension scratch. -/
  fresh : ∀ x : Fin T, eb d eX pX gW X NS + u ≤ x.val → x.val < eb d eX pX gW X NS + NE →
    A' x = List.replicate Rc false ∧ H' x = 0

include pl in
/-- The extension scratch fits in the universe. -/
theorem ext_lt {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (k : Nat) (hk : k < NE) : eb d eX pX gW X NS + k < T := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have := hE.hres; have := pl.hT
  unfold eb; omega

include pl hh in
/-- A strip tape fits in the universe. -/
theorem strip_lt (i : Nat) (hi : i < 32) : sb d eX pX gW + i < T := by
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := pl.zlay hh
  unfold ZB at z1 z2; unfold sb; omega

/-- An extension tape. -/
def extT {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (k : Nat) (hk : k < NE) : Fin T :=
  ⟨eb d eX pX gW X NS + k, ext_lt pl hE k hk⟩

/-- A strip tape. -/
def stripT (i : Nat) (hi : i < 32) : Fin T := ⟨sb d eX pX gW + i, strip_lt pl hh i hi⟩

/-- **Start**: `initS`'s exit is the invariant with nothing written and nothing used. -/
theorem start (NR NE : Nat) (hNR8 : 8 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    (L cS cR q b Rc Vv CP CW CL DP DW DL : Nat) (mode : Bool) (tg : Nat)
    (H H1 : Fin T → ℕ) (A A1 : Fin T → List Bool)
    (ho : InitOutS pl hh NR L cS cR q b Rc Vv CP CW CL DP DW DL mode tg H A H1 A1) :
    InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg (fun _ => none) 0 H A H1 A1 := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hBG : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  refine ⟨⟨H1, A1, ho, fun _ _ _ => ⟨rfl, rfl⟩⟩, ?_, ?_, ?_⟩
  · intro x h1 h2
    rw [slotVal_none Rc _ _ rfl]
    exact ho.blank x (by unfold sb at h1; omega) (by unfold sb at h2; omega) (by unfold KeptS sb at *; omega)
  · intro x h1 h2; omega
  · intro x h1 h2
    exact ho.blank x (by unfold eb at h1; omega) (by unfold eb at h2; omega) (by unfold KeptS sb eb at *; omega)

/-- **One resident stage** (heads unchanged): it writes strip slots (`val'`) and a fresh block `[eb+u, eb+u')` of the extension
scratch, nothing else. -/
theorem step {NR NE : Nat} (hNR : NR ≤ 32) {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (A'' : Fin T → List Bool) (val' : Nat → Option (List Bool)) (u' : Nat) (hu : u ≤ u') (hu' : u' ≤ NE)
    (hframe : ∀ x : Fin T, ¬ (sb d eX pX gW + 8 ≤ x.val ∧ x.val < sb d eX pX gW + NR) →
      ¬ (eb d eX pX gW X NS + u ≤ x.val ∧ x.val < eb d eX pX gW X NS + u') → A'' x = A' x)
    (hstrip : ∀ x : Fin T, sb d eX pX gW + 8 ≤ x.val → x.val < sb d eX pX gW + NR →
      A'' x = slotVal Rc val' (x.val - sb d eX pX gW))
    (hext : ∀ x : Fin T, eb d eX pX gW X NS + u ≤ x.val → x.val < eb d eX pX gW X NS + u' → Rc ≤ (A'' x).length) :
    InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val' u' H A H' A'' := by
  have hsb : sb d eX pX gW + NR ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  refine ⟨⟨H1, A1, ho, fun x h1 h2 => ?_⟩, fun x h1 h2 => ⟨hstrip x h1 h2, (hi.strip x h1 h2).2⟩, ?_, ?_⟩
  · rw [hframe x h1 (by omega)]; exact hag x h1 h2
  · intro x h1 h2
    by_cases c : x.val < eb d eX pX gW X NS + u
    · rw [hframe x (by omega) (by omega)]; exact hi.used x h1 c
    · exact ⟨hext x (by omega) h2, (hi.fresh x (by omega) (by omega)).2⟩
  · intro x h1 h2
    rw [hframe x (by omega) (by omega)]
    exact hi.fresh x (by omega) h2

/-- The fixed part of the bank under the invariant (for stage inputs). -/
theorem fixedOf {NR NE : Nat} {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A') :
    (A' (d.scr pl.hT 11) = List.replicate Rc true ∧ H' (d.scr pl.hT 11) = 0) ∧
    (A' (Dims.rsT pl.ext.rest pl.hT 4) = ZeroPadding.pad Rc (List.replicate q true) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 4) = 0) := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  have e11 := hag (d.scr pl.hT 11) (by show ¬ (_ ≤ d.scrV 11 ∧ _); unfold sb; omega)
    (by show ¬ (_ ≤ d.scrV 11 ∧ _); unfold eb; omega)
  have e4 := hag (Dims.rsT pl.ext.rest pl.hT 4)
    (by show ¬ (_ ≤ d.B + 19 + restPc eX pX gW + 4 ∧ _); unfold sb; omega)
    (by show ¬ (_ ≤ d.B + 19 + restPc eX pX gW + 4 ∧ _); unfold eb; omega)
  rw [e11.1, e11.2, e4.1, e4.2]
  exact ⟨ho.drv, ho.qres⟩

/-- S's outer-clear capacity. -/
abbrev Rk (Rc : Nat) : Nat := 16 * (Rc + 1)

/-- **The `Rk` stage**: `1^(16(Rc+1))` from `scr 11` onto the extension tape `u`, then the copier onto `hrT 10` (log `hrT 11`),
blank `b0 = ` extension tape `u+17`; workspace `[u+1, u+17)`. -/
def rkM {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (u : Nat) (hu : u + 18 ≤ NE) :=
  Composition.machine
    (polyAtM (d.scr pl.hT 11) (extT pl hE u (by omega)) (eb d eX pX gW X NS + u + 1) 1 16 (by
      have := ext_lt pl hE (u + 17) (by omega); omega))
    (copyAtM (extT pl hE u (by omega)) (extT pl hE (u + 17) (by omega)) (stripT pl hh 10 (by decide))
      (stripT pl hh 11 (by decide)))

def rkCost (Rc : Nat) : Nat := PCPSerializerCapacity.Power.budget 1 16 Rc + 1 + (2 * Rk Rc + 6)

/-- The `D` stage: `pad Rc 1^(CD(q+1)^DD)` from `rsT 4` onto `hrD` (strip slot 12), workspace `[u, u+14+2DD)`. -/
def dM {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (u DD CD : Nat) (hu : u + 14 + 2*DD ≤ NE) :=
  polyAtM (Dims.rsT pl.ext.rest pl.hT 4) (stripT pl hh 12 (by decide)) (eb d eX pX gW X NS + u) DD CD (by
    have := ext_lt pl hE (u + 13 + 2*DD) (by omega); omega)

theorem rk_step {NR NE : Nat} (hNR13 : 13 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} (hu : u + 18 ≤ NE) {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (h10 : val 10 = none) (h11 : val 11 = none) :
    ∃ A'', Step (rkM pl hh hE u hu) (rkCost Rc) H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun i => if i = 10 then some (List.replicate (Rk Rc) true)
          else if i = 11 then some (List.replicate (Rk Rc + 2) false) else val i) (u + 18) H A H' A'' := by
  obtain ⟨hF0, hB0, h11', h12', hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  obtain ⟨⟨hdA, hdH⟩, _⟩ := fixedOf pl hh hi
  have v11 : (d.scr pl.hT 11).val = d.scrV 11 := rfl
  have vs : ∀ i hi', (stripT pl hh i hi').val = sb d eX pX gW + i := fun _ _ => rfl
  have ve : ∀ k hk, (extT pl hE k hk).val = eb d eX pX gW X NS + k := fun _ _ => rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  -- the polynomial `16·(Rc+1)`
  have fr : ∀ x : Fin T, eb d eX pX gW X NS + u ≤ x.val → x.val < eb d eX pX gW X NS + NE →
      A' x = List.replicate Rc false ∧ H' x = 0 := fun x h1 h2 => hi.fresh x h1 h2
  have strip0 : ∀ i (hi' : i < 32), 8 ≤ i → i < NR → val i = none →
      A' (stripT pl hh i hi') = List.replicate Rc false ∧ H' (stripT pl hh i hi') = 0 := by
    intro i hi' h8 hN hv
    have := hi.strip (stripT pl hh i hi') (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + i - sb d eX pX gW = i by omega, slotVal_none Rc val i hv] at this
    exact this
  obtain ⟨A1, s1, o1, w1, f1⟩ := polyAt_run 1 16 Rc Rc (d.scr pl.hT 11) (extT pl hE u (by omega))
    (eb d eX pX gW X NS + u + 1) (by have := ext_lt pl hE (u + 17) (by omega); omega)
    (by rw [v11, ve]; unfold eb; omega) (by rw [v11]; unfold eb; omega) (by rw [ve]; omega) H' A' hdH
    ((fr _ (by rw [ve]) (by rw [ve]; omega)).2) (fun x h1 h2 => (fr x (by omega) (by omega)).2)
    (by rw [hdA]; simp [ZeroPadding.pad]) ((fr _ (by rw [ve]) (by rw [ve]; omega)).1)
    (fun x h1 h2 => (fr x (by omega) (by omega)).1)
  have o1' : A1 (extT pl hE u (by omega)) = List.replicate (Rk Rc) true := by
    rw [o1, pow_one]; simp [ZeroPadding.pad, Rk]; omega
  -- the copier onto `hrT 10 / 11`
  have nb : ∀ x : Fin T, x ≠ extT pl hE u (by omega) →
      ¬ (eb d eX pX gW X NS + u + 1 ≤ x.val ∧ x.val < eb d eX pX gW X NS + u + 1 + 14 + 2*1) → A1 x = A' x := f1
  have b0A : A1 (extT pl hE (u + 17) (by omega)) = List.replicate Rc false := by
    rw [nb _ (fun h => by have := congrArg Fin.val h; rw [ve, ve] at this; omega) (by rw [ve]; omega)]
    exact (fr _ (by rw [ve]; omega) (by rw [ve]; omega)).1
  have d10 := strip0 10 (by decide) (by decide) (by omega) h10
  have d11 := strip0 11 (by decide) (by decide) (by omega) h11
  have s10 : A1 (stripT pl hh 10 (by decide)) = List.replicate Rc false := by
    rw [nb _ (fun h => by have := congrArg Fin.val h; rw [vs, ve] at this; omega) (by rw [vs]; omega)]
    exact d10.1
  have s11 : A1 (stripT pl hh 11 (by decide)) = List.replicate Rc false := by
    rw [nb _ (fun h => by have := congrArg Fin.val h; rw [vs, ve] at this; omega) (by rw [vs]; omega)]
    exact d11.1
  obtain ⟨A2, s2, o2d, o2l, f2⟩ := copyAt_run (Rk Rc) Rc (by unfold Rk; omega) (extT pl hE u (by omega))
    (extT pl hE (u + 17) (by omega)) (stripT pl hh 10 (by decide)) (stripT pl hh 11 (by decide))
    (by rw [ve, ve]; omega) (by rw [ve, vs]; omega) (by rw [ve, vs]; omega) (by rw [ve, vs]; omega)
    (by rw [ve, vs]; omega) (by rw [vs, vs]; omega) H' A1
    ((fr _ (by rw [ve]) (by rw [ve]; omega)).2) ((fr _ (by rw [ve]; omega) (by rw [ve]; omega)).2) d10.2 d11.2
    o1' b0A s10 s11
  refine ⟨A2, s1.seq s2, step pl hh hNR hi A2 _ (u + 18) (by omega) hu ?_ ?_ ?_⟩
  · intro x h1 h2
    have n10 : x ≠ stripT pl hh 10 (by decide) := fun h => h1 (by rw [h, vs]; omega)
    have n11 : x ≠ stripT pl hh 11 (by decide) := fun h => h1 (by rw [h, vs]; omega)
    rw [f2 x n10 n11]
    exact nb x (fun h => h2 (by rw [h, ve]; omega)) (by omega)
  · intro x h1 h2
    by_cases c10 : x.val = sb d eX pX gW + 10
    · have e : x = stripT pl hh 10 (by decide) := Fin.ext (by rw [vs]; exact c10)
      rw [e, o2d, vs, show sb d eX pX gW + 10 - sb d eX pX gW = 10 by omega]
      simp [slotVal]
    by_cases c11 : x.val = sb d eX pX gW + 11
    · have e : x = stripT pl hh 11 (by decide) := Fin.ext (by rw [vs]; exact c11)
      rw [e, o2l, vs, show sb d eX pX gW + 11 - sb d eX pX gW = 11 by omega]
      simp [slotVal]
    · have n10 : x ≠ stripT pl hh 10 (by decide) := fun h => c10 (by rw [h, vs])
      have n11 : x ≠ stripT pl hh 11 (by decide) := fun h => c11 (by rw [h, vs])
      rw [f2 x n10 n11, nb x (fun h => by rw [h, ve] at h2; omega) (by omega), (hi.strip x h1 h2).1]
      have a10 : x.val - sb d eX pX gW ≠ 10 := by omega
      have a11 : x.val - sb d eX pX gW ≠ 11 := by omega
      simp only [slotVal, if_neg a10, if_neg a11]
  · intro x h1 h2
    by_cases c0 : x = extT pl hE u (by omega)
    · rw [f2 x (fun h => by have := congrArg Fin.val (c0.symm.trans h); rw [ve, vs] at this; omega)
        (fun h => by have := congrArg Fin.val (c0.symm.trans h); rw [ve, vs] at this; omega), c0, o1']
      simp [Rk]; omega
    by_cases c17 : x.val = eb d eX pX gW X NS + u + 17
    · have n10 : x ≠ stripT pl hh 10 (by decide) := fun h => by rw [h, vs] at c17; omega
      have n11 : x ≠ stripT pl hh 11 (by decide) := fun h => by rw [h, vs] at c17; omega
      rw [f2 x n10 n11, nb x c0 (by omega), (fr x (by omega) (by omega)).1]
      simp
    · have n10 : x ≠ stripT pl hh 10 (by decide) := fun h => by rw [h, vs] at h1; omega
      have n11 : x ≠ stripT pl hh 11 (by decide) := fun h => by rw [h, vs] at h1; omega
      have c0' : x.val ≠ eb d eX pX gW X NS + u := fun h => c0 (Fin.ext (by rw [ve]; exact h))
      rw [f2 x n10 n11]
      exact w1 x (by omega) (by omega)

theorem d_step {NR NE : Nat} (hNR13 : 13 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} (DD CD : Nat) (hu : u + 14 + 2*DD ≤ NE)
    {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (h12 : val 12 = none) :
    ∃ A'', Step (dM pl hh hE u DD CD hu) (PCPSerializerCapacity.Power.budget DD CD q) H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun i => if i = 12 then some (ZeroPadding.pad Rc (List.replicate (CD*(q+1)^DD) true)) else val i)
        (u + 14 + 2*DD) H A H' A'' := by
  obtain ⟨hF0, hB0, h11', h12', hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  obtain ⟨_, ⟨hqA, hqH⟩⟩ := fixedOf pl hh hi
  have v4 : (Dims.rsT pl.ext.rest pl.hT 4).val = d.B + 19 + restPc eX pX gW + 4 := rfl
  have vs : ∀ i hi', (stripT pl hh i hi').val = sb d eX pX gW + i := fun _ _ => rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  have fr : ∀ x : Fin T, eb d eX pX gW X NS + u ≤ x.val → x.val < eb d eX pX gW X NS + NE →
      A' x = List.replicate Rc false ∧ H' x = 0 := fun x h1 h2 => hi.fresh x h1 h2
  have d12 : A' (stripT pl hh 12 (by decide)) = List.replicate Rc false ∧ H' (stripT pl hh 12 (by decide)) = 0 := by
    have := hi.strip (stripT pl hh 12 (by decide)) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + 12 - sb d eX pX gW = 12 by omega, slotVal_none Rc val 12 h12] at this
    exact this
  obtain ⟨A1, s1, o1, w1, f1⟩ := polyAt_run DD CD q Rc (Dims.rsT pl.ext.rest pl.hT 4) (stripT pl hh 12 (by decide))
    (eb d eX pX gW X NS + u) (by have := ext_lt pl hE (u + 13 + 2*DD) (by omega); omega)
    (by rw [v4, vs]; omega) (by rw [v4]; unfold eb; omega) (by rw [vs]; omega) H' A' hqH d12.2
    (fun x h1 h2 => (fr x h1 (by omega)).2) hqA d12.1 (fun x h1 h2 => (fr x h1 (by omega)).1)
  refine ⟨A1, s1, step pl hh hNR hi A1 _ (u + 14 + 2*DD) (by omega) hu ?_ ?_ ?_⟩
  · intro x h1 h2
    exact f1 x (fun h => h1 (by rw [h, vs]; omega)) (by omega)
  · intro x h1 h2
    by_cases c : x.val = sb d eX pX gW + 12
    · have e : x = stripT pl hh 12 (by decide) := Fin.ext (by rw [vs]; exact c)
      rw [e, o1, vs, show sb d eX pX gW + 12 - sb d eX pX gW = 12 by omega]
      simp [slotVal]
    · rw [f1 x (fun h => c (by rw [h, vs])) (by omega), (hi.strip x h1 h2).1]
      have a12 : x.val - sb d eX pX gW ≠ 12 := by omega
      simp only [slotVal, if_neg a12]
  · intro x h1 h2
    exact w1 x h1 (by omega)

/-- A written strip slot, read back (heads 0). -/
theorem slot_of {NR NE : Nat} {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (i : Nat) (hi32 : i < 32) (h8 : 8 ≤ i) (hN : i < NR) (w : List Bool) (hw : val i = some w) :
    A' (stripT pl hh i hi32) = w ∧ H' (stripT pl hh i hi32) = 0 := by
  have vs : (stripT pl hh i hi32).val = sb d eX pX gW + i := rfl
  have := hi.strip (stripT pl hh i hi32) (by rw [vs]; omega) (by rw [vs]; omega)
  rw [vs, show sb d eX pX gW + i - sb d eX pX gW = i by omega, slotVal_some Rc val i w hw] at this
  exact this

/-! ## 4. The init with these residents -/

/-- The resident map of `initRMachine`. -/
def valR (Rc DD CD q : Nat) : Nat → Option (List Bool) := fun i =>
  if i = 12 then some (ZeroPadding.pad Rc (List.replicate (CD*(q+1)^DD) true))
  else if i = 10 then some (List.replicate (Rk Rc) true)
  else if i = 11 then some (List.replicate (Rk Rc + 2) false) else none

def initRCost (L C cVc cS cR DP CP DW CW DL CL : Nat) (mode : Bool) (target q b DD CD : Nat) : Nat :=
  initSCost pl L C cVc cS cR DP CP DW CW DL CL mode target q b + 1 + rkCost (Once.Rc eR L C q) + 1 +
    PCPSerializerCapacity.Power.budget DD CD q

end
end NearCubicWires.SourceSkeleton.InitS
end
