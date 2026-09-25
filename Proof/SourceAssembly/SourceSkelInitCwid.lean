import Proof.SourceAssembly.SourceSkelInitHorner
import Proof.SourceAssembly.SourceRequestSymOriginal

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

/-! ## 1. The two widths as Horner coefficient lists -/

/-- THR (`codeWidth`): coefficients of `Ld^14 .. Ld^0` (the leading `Ld^15` coefficient is `4096`). -/
def thrCs : List Nat := [4096, 0, 0, 0, 36864, 33792, 0, 0, 0, 82472, 51568, 560, 640, 360, 50596]
/-- SYM (`symCodeWidth`). -/
def symCs : List Nat := [4096, 0, 0, 0, 28672, 25600, 0, 0, 0, 25640, 880, 560, 640, 360, 676]

def cwCs (mode : Bool) : List Nat := if mode then symCs else thrCs

def cwidOf (mode : Bool) (L : Nat) : Nat :=
  if mode then SourceRequest.SymOriginal.symCodeWidth L else SourceRequest.ThrSwitch.codeWidth L

theorem thr_eq (p : Nat) : hVal p thrCs 4096 = SourceRequest.ThrSwitch.codeWidth p := by
  simp only [hVal, thrCs, SourceRequest.ThrSwitch.codeWidth,
    RecoveryWitnessPolicy.canonicalThresholdCircuitCodeBitBound, RecoveryWitnessPolicy.taggedListBitBound,
    RecoveryWitnessPolicy.canonicalNatCodeBitBound, CanonicalBinary.encodeNatBitsBound,
    RecoveryWitnessPolicy.canonicalBalancedCodeBitBound, RecoveryWitnessPolicy.canonicalSupportedGateCodeBitBound,
    RecoveryWitnessPolicy.canonicalIntCodeBitBound]
  ring

theorem sym_eq (p : Nat) : hVal p symCs 4096 = SourceRequest.SymOriginal.symCodeWidth p := by
  simp only [hVal, symCs, SourceRequest.SymOriginal.symCodeWidth,
    RecoveryWitnessPolicy.canonicalSymmetricCircuitCodeBitBound, RecoveryWitnessPolicy.taggedListBitBound,
    RecoveryWitnessPolicy.canonicalNatCodeBitBound, CanonicalBinary.encodeNatBitsBound,
    RecoveryWitnessPolicy.canonicalBalancedCodeBitBound, RecoveryWitnessPolicy.canonicalSupportedGateCodeBitBound,
    RecoveryWitnessPolicy.canonicalIntCodeBitBound]
  ring

/-- **The width identity.** -/
theorem cwid_eq (mode : Bool) (p : Nat) : hVal p (cwCs mode) 4096 = cwidOf mode p := by
  cases mode
  · exact thr_eq p
  · exact sym_eq p

theorem cwCs_length (mode : Bool) : (cwCs mode).length = 15 := by cases mode <;> rfl

theorem cwCs_le (mode : Bool) (Rc : Nat) (h : 82472 ≤ Rc) : ∀ a, a ∈ cwCs mode → a ≤ Rc := by
  intro a ha
  cases mode <;> simp [cwCs, thrCs, symCs] at ha <;> omega

theorem hOut_eq {T : Nat} (f : Nat → Fin T) : ∀ (cs : List Nat) (V : Fin T) (u : Nat), cs ≠ [] →
    hOut f cs V u = f (u + 5 * cs.length - 2) := by
  intro cs
  induction cs with
  | nil => intro V u h; exact absurd rfl h
  | cons a cs ih =>
    intro V u _
    by_cases hc : cs = []
    · subst hc
      show f (u + 3) = f (u + 5 * 1 - 2)
      exact congrArg f (by omega)
    · show hOut f cs (f (u+3)) (u+5) = _
      rw [ih (f (u+3)) (u+5) hc]
      exact congrArg f (by simp only [List.length_cons]; omega)

/-! ## 2. The stage on the init's invariant -/

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

include pl in
theorem T_pos : 0 < T := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have := pl.hT; omega

/-- A total extension-tape map (the value is `eb + k` whenever that is a tape). -/
def extF (k : Nat) : Fin T := ⟨(eb d eX pX gW X NS + k) % T, Nat.mod_lt _ (T_pos pl)⟩

theorem extF_val {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (k : Nat) (hk : k < NE) :
    (extF (NS := NS) pl k).val = eb d eX pX gW X NS + k :=
  Nat.mod_eq_of_lt (ext_lt pl hE k hk)

/-- The stage: template of `Ld` onto `u`, log `u+1`; `1^4096` onto `u+3` (word log `u+2`); Horner on `[u+4, u+79)`; copy onto `hrT 8`
(blank `u+79`, log `u+80`). -/
def cwM (mode : Bool) (u : Nat) :=
  Composition.machine
    (RecoveryFocus.machine (![Dims.hrT (ext3 pl hh) pl.hT 3, extF (NS := NS) pl u, extF (NS := NS) pl (u+1)] : Fin 3 → Fin T)
      (DimensionTemplate.machine false))
  (Composition.machine
    (RecoveryFocus.machine (![extF (NS := NS) pl (u+3), extF (NS := NS) pl (u+2)] : Fin 2 → Fin T)
      (HierarchyFixedWord.machine (List.replicate 4096 true)))
  (Composition.machine
    (hChain (extF (NS := NS) pl) (extF (NS := NS) pl u) (extF (NS := NS) pl (u+2)) (cwCs mode)
      (extF (NS := NS) pl (u+3)) (u+4)).2
    (RecoveryFocus.machine (![extF (NS := NS) pl (u+77), extF (NS := NS) pl (u+79), stripT pl hh 8 (by decide),
      extF (NS := NS) pl (u+80)] : Fin 4 → Fin T) ClockUnarySum.machine)))

def cwCost (mode : Bool) (Ld : Nat) : Nat :=
  (2*Ld+8) + 1 + ((2 * (List.replicate 4096 true).length + 2) + 1 +
    (hCost Ld (cwCs mode) 4096 + 1 + (2 * cwidOf mode Ld + 6)))

/-- The value of `hrT 3` under the invariant (SI's cap `Ld`). -/
theorem fixed3 {NR NE : Nat} {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A') :
    A' (Dims.hrT (ext3 pl hh) pl.hT 3) = ZeroPadding.pad Rc (List.replicate (CL*(q+1)^DL) true) ∧
      H' (Dims.hrT (ext3 pl hh) pl.hT 3) = 0 := by
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  have v3 : (Dims.hrT (ext3 pl hh) pl.hT 3).val = sb d eX pX gW + 3 := rfl
  have e3 := hag (Dims.hrT (ext3 pl hh) pl.hT 3) (by rw [v3]; omega) (by rw [v3]; unfold sb eb; omega)
  rw [e3.1, e3.2]
  exact ho.z3

/-- **The `1^cwid` stage** on the init's invariant. -/
theorem cw_step {NR NE : Nat} (hNR9 : 9 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} (hu : u + 81 ≤ NE) {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (h8 : val 8 = none) (hLd : CL*(q+1)^DL + 2 ≤ Rc) (hRc : 82472 ≤ Rc) :
    ∃ A'', Step (cwM pl hh mode u) (cwCost mode (CL*(q+1)^DL)) H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun i => if i = 8 then some (ZeroPadding.pad Rc (List.replicate (cwidOf mode (CL*(q+1)^DL)) true)) else val i)
        (u + 81) H A H' A'' := by
  obtain ⟨hF0, hB0, h11', h12', hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  set Ld := CL*(q+1)^DL with hLdd
  set f := extF (NS := NS) pl with hfd
  set e := eb d eX pX gW X NS with hed
  have fv : ∀ k, k < NE → (f k).val = e + k := fun k hk => extF_val pl hE k hk
  have vs : ∀ i hi', (stripT pl hh i hi').val = sb d eX pX gW + i := fun _ _ => rfl
  have v3 : (Dims.hrT (ext3 pl hh) pl.hT 3).val = sb d eX pX gW + 3 := rfl
  obtain ⟨h3A, h3H⟩ := fixed3 pl hh hi
  have fr : ∀ k, u ≤ k → k < NE → A' (f k) = List.replicate Rc false ∧ H' (f k) = 0 := fun k h1 h2 =>
    hi.fresh (f k) (by rw [fv k h2]; omega) (by rw [fv k h2]; omega)
  have s8 : A' (stripT pl hh 8 (by decide)) = List.replicate Rc false ∧ H' (stripT pl hh 8 (by decide)) = 0 := by
    have := hi.strip (stripT pl hh 8 (by decide)) (by rw [vs]) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + 8 - sb d eX pX gW = 8 by omega, slotVal_none Rc val 8 h8] at this
    exact this
  -- template of `Ld` onto `f u` (log `f (u+1)`)
  obtain ⟨A1, s1, oT, oTL, f1⟩ := tmplAt_run Ld Rc hLd (Dims.hrT (ext3 pl hh) pl.hT 3) (f u) (f (u+1))
    (by rw [v3, fv u (by omega)]; omega) (by rw [v3, fv (u+1) (by omega)]; omega)
    (by rw [fv u (by omega), fv (u+1) (by omega)]; omega) H' A' h3H (fr u le_rfl (by omega)).2
    (fr (u+1) (by omega) (by omega)).2 h3A (fr u le_rfl (by omega)).1 (fr (u+1) (by omega) (by omega)).1
  have k1 : ∀ k, u + 2 ≤ k → k < NE → A1 (f k) = List.replicate Rc false := by
    intro k h1 h2
    rw [f1 _ (ne_of_val (by rw [fv k h2, fv u (by omega)]; omega)) (ne_of_val (by rw [fv k h2, fv (u+1) (by omega)]; omega))]
    exact (fr k (by omega) h2).1
  -- the leading coefficient `1^4096` onto `f (u+3)` (log `f (u+2)`)
  have s2 := word_step (List.replicate 4096 true) (f (u+3)) (f (u+2))
    (ne_of_val (by rw [fv (u+3) (by omega), fv (u+2) (by omega)]; omega)) Rc Rc
    (by rw [List.length_replicate]; omega) H' A1 (fr (u+3) (by omega) (by omega)).2 (fr (u+2) (by omega) (by omega)).2
    (k1 (u+3) (by omega) (by omega)) (k1 (u+2) (by omega) (by omega))
  set A2 := Function.update A1 (f (u+3)) (ZeroPadding.pad Rc (List.replicate 4096 true)) with hA2
  have up : ∀ x : Fin T, x ≠ f (u+3) → A2 x = A1 x := fun x hx => Function.update_of_ne hx _ _
  -- Horner on `[u+4, u+79)`
  obtain ⟨A3, s3, o3, l3, fr3⟩ := horner_run Rc Ld f e (f u) (f (u+2)) (cwCs mode) 4096 (f (u+3)) (u+4) H' A2
    (fun k h1 h2 => fv k (by rw [cwCs_length] at h2; omega)) (cwCs_le mode Rc hRc)
    (by rw [fv u (by omega)]; omega) (by rw [fv (u+2) (by omega)]; omega) (by rw [fv (u+3) (by omega)]; omega)
    (by rw [fv u (by omega), fv (u+2) (by omega)]; omega) (by rw [fv u (by omega), fv (u+3) (by omega)]; omega)
    (by rw [fv (u+2) (by omega), fv (u+3) (by omega)]; omega)
    (fr u le_rfl (by omega)).2 (fr (u+2) (by omega) (by omega)).2 (fr (u+3) (by omega) (by omega)).2
    (fun k h1 h2 => (fr k (by omega) (by rw [cwCs_length] at h2; omega)).2)
    (by rw [up _ (ne_of_val (by rw [fv u (by omega), fv (u+3) (by omega)]; omega))]; exact oT)
    (by rw [up _ (ne_of_val (by rw [fv (u+2) (by omega), fv (u+3) (by omega)]; omega))]
        exact k1 (u+2) (by omega) (by omega))
    (Function.update_self _ _ _)
    (fun k h1 h2 => by
      rw [cwCs_length] at h2
      rw [up _ (ne_of_val (by rw [fv k (by omega), fv (u+3) (by omega)]; omega))]
      exact k1 k (by omega) (by omega))
  rw [cwCs_length, cwid_eq] at *
  have hout : hOut f (cwCs mode) (f (u+3)) (u+4) = f (u+77) := by
    rw [hOut_eq f _ _ _ (by cases mode <;> simp [cwCs, thrCs, symCs]), cwCs_length]
    exact congrArg f (by omega)
  rw [hout] at o3
  -- the copy onto `hrT 8` (blank `f (u+79)`, log `f (u+80)`)
  have k3 : ∀ k, u + 79 ≤ k → k < NE → A3 (f k) = List.replicate Rc false := by
    intro k h1 h2
    rw [fr3 _ (by rw [fv k h2]; omega), up _ (ne_of_val (by rw [fv k h2, fv (u+3) (by omega)]; omega))]
    exact k1 k (by omega) h2
  have a8 : A3 (stripT pl hh 8 (by decide)) = List.replicate Rc false := by
    rw [fr3 _ (by rw [vs]; omega), up _ (ne_of_val (by rw [vs, fv (u+3) (by omega)]; omega)),
      f1 _ (ne_of_val (by rw [vs, fv u (by omega)]; omega)) (ne_of_val (by rw [vs, fv (u+1) (by omega)]; omega))]
    exact s8.1
  obtain ⟨A4, s4, o4, l4, f4⟩ := copyPadAt_run (cwidOf mode Ld) Rc (f (u+77)) (f (u+79)) (stripT pl hh 8 (by decide))
    (f (u+80)) (by rw [fv (u+77) (by omega), fv (u+79) (by omega)]; omega)
    (by rw [fv (u+77) (by omega), vs]; omega) (by rw [fv (u+77) (by omega), fv (u+80) (by omega)]; omega)
    (by rw [fv (u+79) (by omega), vs]; omega) (by rw [fv (u+79) (by omega), fv (u+80) (by omega)]; omega)
    (by rw [vs, fv (u+80) (by omega)]; omega) H' A3 (fr (u+77) (by omega) (by omega)).2
    (fr (u+79) (by omega) (by omega)).2 s8.2 (fr (u+80) (by omega) (by omega)).2 o3
    (k3 (u+79) (by omega) (by omega)) a8 (k3 (u+80) (by omega) (by omega))
  refine ⟨A4, s1.seq (s2.seq (s3.seq s4)), step pl hh hNR hi A4 _ (u + 81) (by omega) hu ?_ ?_ ?_⟩
  · -- frame: off the strip and off `[e+u, e+u+81)`
    intro x h1 h2
    have n8 : x ≠ stripT pl hh 8 (by decide) := fun h => h1 (by rw [h, vs]; omega)
    have nL : x ≠ f (u+80) := ne_of_val (by rw [fv (u+80) (by omega)]; omega)
    rw [f4 x n8 nL, fr3 x (by omega), up x (ne_of_val (by rw [fv (u+3) (by omega)]; omega)),
      f1 x (ne_of_val (by rw [fv u (by omega)]; omega)) (ne_of_val (by rw [fv (u+1) (by omega)]; omega))]
  · intro x h1 h2
    by_cases c8 : x.val = sb d eX pX gW + 8
    · have ex : x = stripT pl hh 8 (by decide) := Fin.ext (by rw [vs]; exact c8)
      rw [ex, o4, vs, show sb d eX pX gW + 8 - sb d eX pX gW = 8 by omega]
      simp [slotVal]
    · have n8 : x ≠ stripT pl hh 8 (by decide) := fun h => c8 (by rw [h, vs])
      have nL : x ≠ f (u+80) := ne_of_val (by rw [fv (u+80) (by omega)]; omega)
      rw [f4 x n8 nL, fr3 x (by omega), up x (ne_of_val (by rw [fv (u+3) (by omega)]; omega)),
        f1 x (ne_of_val (by rw [fv u (by omega)]; omega)) (ne_of_val (by rw [fv (u+1) (by omega)]; omega)),
        (hi.strip x h1 h2).1]
      have a8' : x.val - sb d eX pX gW ≠ 8 := by omega
      simp only [slotVal, if_neg a8']
  · intro x h1 h2
    have hk : x = f (x.val - e) := Fin.ext (by rw [fv _ (by omega)]; omega)
    by_cases c80 : x.val = e + u + 80
    · rw [hk, show x.val - e = u + 80 by omega]; exact l4
    have n80 : x ≠ f (u+80) := ne_of_val (by rw [fv (u+80) (by omega)]; omega)
    have n8 : x ≠ stripT pl hh 8 (by decide) := ne_of_val (by rw [vs]; omega)
    rw [f4 x n8 n80]
    by_cases cH : e + u + 4 ≤ x.val ∧ x.val < e + u + 79
    · rw [hk]; exact l3 (x.val - e) (by omega) (by omega)
    rw [fr3 x (by omega)]
    by_cases c3 : x.val = e + u + 3
    · rw [hk, show x.val - e = u + 3 by omega, hA2, Function.update_self]; exact Uniform.long_pad Rc _
    rw [up x (ne_of_val (by rw [fv (u+3) (by omega)]; omega))]
    by_cases c0 : x.val = e + u
    · rw [hk, show x.val - e = u by omega, oT]; exact Uniform.long_pad Rc _
    by_cases c1 : x.val = e + u + 1
    · rw [hk, show x.val - e = u + 1 by omega]; exact oTL
    · rw [f1 x (ne_of_val (by rw [fv u (by omega)]; omega)) (ne_of_val (by rw [fv (u+1) (by omega)]; omega)), hk,
        (fr (x.val - e) (by omega) (by omega)).1]
      simp

end
end NearCubicWires.SourceSkeleton.InitS
end
