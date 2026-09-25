import Proof.SourceAssembly.SourceSkelInitCwid
import Proof.SourceAssembly.SourceRequestCurComp

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

/-! ## 1. `frame` of a unary word -/

theorem frame_ones (k : Nat) : frame (List.replicate k true) = List.replicate (2*k) true ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    show true :: true :: frame (List.replicate k true) = _
    rw [ih, show 2 * (k+1) = (2*k).succ.succ by omega, List.replicate_succ, List.replicate_succ]
    rfl

theorem pad_frame_ones (Rc k : Nat) (h : 2*k + 1 ≤ Rc) :
    ZeroPadding.pad Rc (frame (List.replicate k true)) = ZeroPadding.pad Rc (List.replicate (2*k) true) := by
  rw [frame_ones, ExtDecompositionBatch.pad_exact, ExtDecompositionBatch.pad_exact]
  simp only [List.length_append, List.length_replicate, List.length_singleton, List.append_assoc]
  congr 1
  rw [show Rc - 2*k = (Rc - (2*k + 1)) + 1 by omega]
  rfl

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-! ## 2. A cap `C·(q+1)^D` from `rsT 4` onto any strip slot -/

def polyResM {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (i : Nat) (hi : i < 32) (u Dp Cp : Nat)
    (hu : u + 14 + 2*Dp ≤ NE) :=
  polyAtM (Dims.rsT pl.ext.rest pl.hT 4) (stripT pl hh i hi) (eb d eX pX gW X NS + u) Dp Cp (by
    have := ext_lt pl hE (u + 13 + 2*Dp) (by omega); omega)

theorem polyRes_step {NR NE : Nat} (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} (i : Nat) (hi : i < 32) (hi8 : 8 ≤ i) (hiN : i < NR)
    (Dp Cp : Nat) (hu : u + 14 + 2*Dp ≤ NE)
    {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hinv : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (hv : val i = none) :
    ∃ A'', Step (polyResM pl hh hE i hi u Dp Cp hu) (PCPSerializerCapacity.Power.budget Dp Cp q) H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun j => if j = i then some (ZeroPadding.pad Rc (List.replicate (Cp*(q+1)^Dp) true)) else val j)
        (u + 14 + 2*Dp) H A H' A'' := by
  obtain ⟨hF0, hB0, h11', h12', hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  obtain ⟨_, ⟨hqA, hqH⟩⟩ := fixedOf pl hh hinv
  have v4 : (Dims.rsT pl.ext.rest pl.hT 4).val = d.B + 19 + restPc eX pX gW + 4 := rfl
  have vs : ∀ j hj, (stripT pl hh j hj).val = sb d eX pX gW + j := fun _ _ => rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  have fr : ∀ x : Fin T, eb d eX pX gW X NS + u ≤ x.val → x.val < eb d eX pX gW X NS + NE →
      A' x = List.replicate Rc false ∧ H' x = 0 := fun x h1 h2 => hinv.fresh x h1 h2
  have di : A' (stripT pl hh i hi) = List.replicate Rc false ∧ H' (stripT pl hh i hi) = 0 := by
    have := hinv.strip (stripT pl hh i hi) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + i - sb d eX pX gW = i by omega, slotVal_none Rc val i hv] at this
    exact this
  obtain ⟨A1, s1, o1, w1, f1⟩ := polyAt_run Dp Cp q Rc (Dims.rsT pl.ext.rest pl.hT 4) (stripT pl hh i hi)
    (eb d eX pX gW X NS + u) (by have := ext_lt pl hE (u + 13 + 2*Dp) (by omega); omega)
    (by rw [v4, vs]; omega) (by rw [v4]; unfold eb; omega) (by rw [vs]; omega) H' A' hqH di.2
    (fun x h1 h2 => (fr x h1 (by omega)).2) hqA di.1 (fun x h1 h2 => (fr x h1 (by omega)).1)
  refine ⟨A1, s1, step pl hh hNR hinv A1 _ (u + 14 + 2*Dp) (by omega) hu ?_ ?_ ?_⟩
  · intro x h1 h2
    exact f1 x (fun h => h1 (by rw [h, vs]; omega)) (by omega)
  · intro x h1 h2
    by_cases c : x.val = sb d eX pX gW + i
    · have e : x = stripT pl hh i hi := Fin.ext (by rw [vs]; exact c)
      rw [e, o1, vs, show sb d eX pX gW + i - sb d eX pX gW = i by omega]
      simp [slotVal]
    · rw [f1 x (fun h => c (by rw [h, vs])) (by omega), (hinv.strip x h1 h2).1]
      have ai : x.val - sb d eX pX gW ≠ i := by omega
      simp only [slotVal, if_neg ai]
  · intro x h1 h2
    exact w1 x h1 (by omega)

/-! ## 3. `hrG 0 = pad Rc (frame 1^q)`: copy `rsT 4`, then sum -/

/-- Copy `rsT 4` onto `u` (blank `u+1`, log `u+2`), then `rsT 4 + u` onto strip slot 14 (log `u+3`). -/
def g0M (u : Nat) :=
  Composition.machine
    (RecoveryFocus.machine (![Dims.rsT pl.ext.rest pl.hT 4, extF (NS := NS) pl u, extF (NS := NS) pl (u+2),
      extF (NS := NS) pl (u+1)] : Fin 4 → Fin T) ClockUnarySum.machine)
    (RecoveryFocus.machine (![Dims.rsT pl.ext.rest pl.hT 4, extF (NS := NS) pl (u+2), stripT pl hh 14 (by decide),
      extF (NS := NS) pl (u+3)] : Fin 4 → Fin T) ClockUnarySum.machine)

theorem g0_step {NR NE : Nat} (hNR16 : 16 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} (hu : u + 4 ≤ NE) {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hinv : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (h14 : val 14 = none) (hq : 2*q + 1 ≤ Rc) :
    ∃ A'', Step (g0M pl hh u) ((2*q+6) + 1 + (2*(q+q)+6)) H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun j => if j = 14 then some (ZeroPadding.pad Rc (frame (List.replicate q true))) else val j)
        (u + 4) H A H' A'' := by
  obtain ⟨hF0, hB0, h11', h12', hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  obtain ⟨_, ⟨hqA, hqH⟩⟩ := fixedOf pl hh hinv
  have v4 : (Dims.rsT pl.ext.rest pl.hT 4).val = d.B + 19 + restPc eX pX gW + 4 := rfl
  have vs : ∀ j hj, (stripT pl hh j hj).val = sb d eX pX gW + j := fun _ _ => rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  set f := extF (NS := NS) pl with hfd
  set e := eb d eX pX gW X NS with hed
  have fv : ∀ k, k < NE → (f k).val = e + k := fun k hk => extF_val pl hE k hk
  have fr : ∀ k, u ≤ k → k < NE → A' (f k) = List.replicate Rc false ∧ H' (f k) = 0 := fun k h1 h2 =>
    hinv.fresh (f k) (by rw [fv k h2]; omega) (by rw [fv k h2]; omega)
  have d14 : A' (stripT pl hh 14 (by decide)) = List.replicate Rc false ∧ H' (stripT pl hh 14 (by decide)) = 0 := by
    have := hinv.strip (stripT pl hh 14 (by decide)) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + 14 - sb d eX pX gW = 14 by omega, slotVal_none Rc val 14 h14] at this
    exact this
  obtain ⟨A1, s1, o1, l1, f1⟩ := copyPadAt_run q Rc (Dims.rsT pl.ext.rest pl.hT 4) (f u) (f (u+2)) (f (u+1))
    (by rw [v4, fv u (by omega)]; unfold eb at *; omega) (by rw [v4, fv (u+2) (by omega)]; unfold eb at *; omega)
    (by rw [v4, fv (u+1) (by omega)]; unfold eb at *; omega) (by rw [fv u (by omega), fv (u+2) (by omega)]; omega)
    (by rw [fv u (by omega), fv (u+1) (by omega)]; omega) (by rw [fv (u+2) (by omega), fv (u+1) (by omega)]; omega)
    H' A' hqH (fr u le_rfl (by omega)).2 (fr (u+2) (by omega) (by omega)).2 (fr (u+1) (by omega) (by omega)).2
    hqA (fr u le_rfl (by omega)).1 (fr (u+2) (by omega) (by omega)).1 (fr (u+1) (by omega) (by omega)).1
  have n4 : Dims.rsT pl.ext.rest pl.hT 4 ≠ f (u+2) := ne_of_val (by rw [v4, fv (u+2) (by omega)]; unfold eb at *; omega)
  have n4' : Dims.rsT pl.ext.rest pl.hT 4 ≠ f (u+1) := ne_of_val (by rw [v4, fv (u+1) (by omega)]; unfold eb at *; omega)
  obtain ⟨A2, s2, o2, l2, f2⟩ := sumAt_run q q Rc (Dims.rsT pl.ext.rest pl.hT 4) (f (u+2)) (stripT pl hh 14 (by decide))
    (f (u+3)) (by rw [v4, fv (u+2) (by omega)]; unfold eb at *; omega) (by rw [v4, vs]; omega)
    (by rw [v4, fv (u+3) (by omega)]; unfold eb at *; omega) (by rw [fv (u+2) (by omega), vs]; omega)
    (by rw [fv (u+2) (by omega), fv (u+3) (by omega)]; omega) (by rw [vs, fv (u+3) (by omega)]; omega)
    H' A1 hqH (fr (u+2) (by omega) (by omega)).2 d14.2 (fr (u+3) (by omega) (by omega)).2
    (by rw [f1 _ n4 n4']; exact hqA) o1
    (by rw [f1 _ (ne_of_val (by rw [vs, fv (u+2) (by omega)]; omega)) (ne_of_val (by rw [vs, fv (u+1) (by omega)]; omega))]
        exact d14.1)
    (by rw [f1 _ (ne_of_val (by rw [fv (u+3) (by omega), fv (u+2) (by omega)]; omega))
          (ne_of_val (by rw [fv (u+3) (by omega), fv (u+1) (by omega)]; omega))]
        exact (fr (u+3) (by omega) (by omega)).1)
  refine ⟨A2, s1.seq s2, step pl hh hNR hinv A2 _ (u + 4) (by omega) hu ?_ ?_ ?_⟩
  · intro x h1 h2
    rw [f2 x (fun h => h1 (by rw [h, vs]; omega)) (ne_of_val (by rw [fv (u+3) (by omega)]; omega)),
      f1 x (ne_of_val (by rw [fv (u+2) (by omega)]; omega)) (ne_of_val (by rw [fv (u+1) (by omega)]; omega))]
  · intro x h1 h2
    by_cases c : x.val = sb d eX pX gW + 14
    · have ex : x = stripT pl hh 14 (by decide) := Fin.ext (by rw [vs]; exact c)
      rw [ex, o2, vs, show sb d eX pX gW + 14 - sb d eX pX gW = 14 by omega, pad_frame_ones Rc q hq,
        show q + q = 2 * q by omega]
      simp [slotVal]
    · rw [f2 x (fun h => c (by rw [h, vs])) (ne_of_val (by rw [fv (u+3) (by omega)]; omega)),
        f1 x (ne_of_val (by rw [fv (u+2) (by omega)]; omega)) (ne_of_val (by rw [fv (u+1) (by omega)]; omega)),
        (hinv.strip x h1 h2).1]
      have a14 : x.val - sb d eX pX gW ≠ 14 := by omega
      simp only [slotVal, if_neg a14]
  · intro x h1 h2
    have hk : x = f (x.val - e) := Fin.ext (by rw [fv _ (by omega)]; omega)
    have n14 : x ≠ stripT pl hh 14 (by decide) := ne_of_val (by rw [vs]; omega)
    by_cases c3 : x.val = e + u + 3
    · rw [hk, show x.val - e = u + 3 by omega]; exact l2
    rw [f2 x n14 (ne_of_val (by rw [fv (u+3) (by omega)]; omega))]
    by_cases c2 : x.val = e + u + 2
    · rw [hk, show x.val - e = u + 2 by omega, o1]; exact Uniform.long_pad Rc _
    by_cases c1 : x.val = e + u + 1
    · rw [hk, show x.val - e = u + 1 by omega]; exact l1
    · rw [f1 x (ne_of_val (by rw [fv (u+2) (by omega)]; omega)) (ne_of_val (by rw [fv (u+1) (by omega)]; omega)), hk,
        (fr (x.val - e) (by omega) (by omega)).1]
      simp

/-- The subtraction's dock by value: `0 ↦ rsT 1`, `1 ↦ u` (the `1^2`), `2 ↦` strip slot 15, `j ≥ 3 ↦ u + j - 1`. -/
def subSl (u : Nat) : Fin 9 → Fin T := fun j =>
  if j.val = 0 then Dims.rsT pl.ext.rest pl.hT 1
  else if j.val = 1 then extF (NS := NS) pl u
  else if j.val = 2 then stripT pl hh 15 (by decide)
  else extF (NS := NS) pl (u + j.val - 1)

/-- `1^2` onto `u` (log `u+1`), then `rsT 1 − 1^2` onto strip slot 15. -/
def g1M (u : Nat) :=
  Composition.machine
    (RecoveryFocus.machine (![extF (NS := NS) pl u, extF (NS := NS) pl (u+1)] : Fin 2 → Fin T)
      (HierarchyFixedWord.machine (List.replicate 2 true)))
    (SourceRequest.CurComp.subM (subSl pl hh u))

theorem g1_step {NR NE : Nat} (hNR16 : 16 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} (hu : u + 8 ≤ NE) {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hinv : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (h15 : val 15 = none) (hM : 2 * InitPost.Ms L q + 5 ≤ Rc) :
    ∃ A'', Step (g1M pl hh u) ((2 * (List.replicate 2 true).length + 2) + 1 +
        SourceRequest.CurComp.subCost (InitPost.Ms L q)) H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun j => if j = 15 then some (ZeroPadding.pad Rc (frame (List.replicate (normalizedLiveCount q L) true))) else val j)
        (u + 8) H A H' A'' := by
  obtain ⟨hF0, hB0, h11', h12', hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  have vs : ∀ j hj, (stripT pl hh j hj).val = sb d eX pX gW + j := fun _ _ => rfl
  have v1 : (Dims.rsT pl.ext.rest pl.hT 1).val = d.B + 19 + restPc eX pX gW + 1 := rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  set f := extF (NS := NS) pl with hfd
  set e := eb d eX pX gW X NS with hed
  have fv : ∀ k, k < NE → (f k).val = e + k := fun k hk => extF_val pl hE k hk
  have fr : ∀ k, u ≤ k → k < NE → A' (f k) = List.replicate Rc false ∧ H' (f k) = 0 := fun k h1 h2 =>
    hinv.fresh (f k) (by rw [fv k h2]; omega) (by rw [fv k h2]; omega)
  have d15 : A' (stripT pl hh 15 (by decide)) = List.replicate Rc false ∧ H' (stripT pl hh 15 (by decide)) = 0 := by
    have := hinv.strip (stripT pl hh 15 (by decide)) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + 15 - sb d eX pX gW = 15 by omega, slotVal_none Rc val 15 h15] at this
    exact this
  -- `rsT 1` under the invariant
  have r1 : A' (Dims.rsT pl.ext.rest pl.hT 1) = ZeroPadding.pad Rc (List.replicate (InitPost.Ms L q) true) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 1) = 0 := by
    obtain ⟨H1, A1, ho, hag⟩ := hinv.base
    have e1 := hag (Dims.rsT pl.ext.rest pl.hT 1) (by rw [v1]; omega) (by rw [v1]; unfold eb at *; omega)
    rw [e1.1, e1.2]; exact ho.small
  -- the constant `1^2`
  have s1 := word_step (List.replicate 2 true) (f u) (f (u+1))
    (ne_of_val (by rw [fv u (by omega), fv (u+1) (by omega)]; omega)) Rc Rc
    (by rw [List.length_replicate]; omega) H' A' (fr u le_rfl (by omega)).2 (fr (u+1) (by omega) (by omega)).2
    (fr u le_rfl (by omega)).1 (fr (u+1) (by omega) (by omega)).1
  set A1 := Function.update A' (f u) (ZeroPadding.pad Rc (List.replicate 2 true)) with hA1
  have up : ∀ x : Fin T, x ≠ f u → A1 x = A' x := fun x hx => Function.update_of_ne hx _ _
  -- the dock, by value
  have slv : ∀ j : Fin 9, (subSl pl hh u j).val =
      if j.val = 0 then d.B + 19 + restPc eX pX gW + 1 else if j.val = 1 then e + u
      else if j.val = 2 then sb d eX pX gW + 15 else e + (u + j.val - 1) := by
    intro j
    unfold subSl
    have hj := j.isLt
    split_ifs
    · rfl
    · exact fv u (by omega)
    · rfl
    · exact fv _ (by omega)
  have slinj : Function.Injective (subSl pl hh u) := by
    intro a c hac
    have hv := congrArg Fin.val hac
    rw [slv, slv] at hv
    have ha := a.isLt; have hc := c.isLt
    apply Fin.ext
    split_ifs at hv <;> omega
  have sl0 : subSl pl hh u 0 = Dims.rsT pl.ext.rest pl.hT 1 := rfl
  have sl1 : subSl pl hh u 1 = f u := rfl
  have sl2 : subSl pl hh u 2 = stripT pl hh 15 (by decide) := rfl
  have sl8 : subSl pl hh u 8 = f (u + 7) := rfl
  have slj : ∀ j : Fin 9, 3 ≤ j.val → subSl pl hh u j = f (u + j.val - 1) := by
    intro j hj
    unfold subSl
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  obtain ⟨A2, s2, o2, f2, l2⟩ := SourceRequest.CurComp.sub_step (subSl pl hh u) slinj (InitPost.Ms L q) 2 Rc Rc Rc Rc
    (by unfold InitPost.Ms; omega) (by omega) hM H' A1
    (by
      intro j
      by_cases j0 : j.val = 0
      · rw [show j = 0 from Fin.ext j0, sl0]; exact r1.2
      by_cases j1 : j.val = 1
      · rw [show j = 1 from Fin.ext j1, sl1]; exact (fr u le_rfl (by omega)).2
      by_cases j2 : j.val = 2
      · rw [show j = 2 from Fin.ext j2, sl2]; exact d15.2
      · rw [slj j (by omega)]; exact (fr _ (by omega) (by have := j.isLt; omega)).2)
    (by rw [sl0, up _ (ne_of_val (by rw [v1, fv u (by omega)]; unfold eb at *; omega))]; exact r1.1)
    (by rw [sl1, hA1, Function.update_self])
    (by
      intro j h2 h8
      by_cases j2 : j.val = 2
      · rw [show j = 2 from Fin.ext j2, sl2, up _ (ne_of_val (by rw [vs, fv u (by omega)]; omega))]; exact d15.1
      · rw [slj j (by omega), up _ (ne_of_val (by rw [fv _ (by omega), fv u (by omega)]; omega))]
        exact (fr _ (by omega) (by omega)).1)
    (by rw [sl8, up _ (ne_of_val (by rw [fv _ (by omega), fv u (by omega)]; omega))]; exact (fr _ (by omega) (by omega)).1)
  have hK : InitPost.Ms L q - 2 = 2 * normalizedLiveCount q L := by unfold InitPost.Ms; omega
  have hKR : 2 * normalizedLiveCount q L + 1 ≤ Rc := by unfold InitPost.Ms at hM; omega
  -- a tape off the dock's changed set and off `u`: unchanged
  have keep : ∀ x : Fin T, x ≠ f u → x.val ≠ sb d eX pX gW + 15 →
      ¬ (e + u + 2 ≤ x.val ∧ x.val < e + u + 7) → A2 x = A' x := by
    intro x hxu hx15 hx
    rw [f2 x (by
      intro j h2 h8 hj
      by_cases j2 : j.val = 2
      · rw [show j = 2 from Fin.ext j2, sl2] at hj; exact hx15 (by rw [← hj, vs])
      · rw [slj j (by omega)] at hj
        exact hx ⟨by rw [← hj, fv _ (by omega)]; omega, by rw [← hj, fv _ (by omega)]; omega⟩)]
    exact up x hxu
  refine ⟨A2, s1.seq s2, step pl hh hNR hinv A2 _ (u + 8) (by omega) hu ?_ ?_ ?_⟩
  · intro x h1 h2
    exact keep x (ne_of_val (by rw [fv u (by omega)]; omega)) (by omega) (by omega)
  · intro x h1 h2
    by_cases c : x.val = sb d eX pX gW + 15
    · have ex : x = stripT pl hh 15 (by decide) := Fin.ext (by rw [vs]; exact c)
      rw [ex, vs, show sb d eX pX gW + 15 - sb d eX pX gW = 15 by omega, ← sl2, o2, hK,
        ← pad_frame_ones Rc _ hKR]
      simp [slotVal]
    · rw [keep x (ne_of_val (by rw [fv u (by omega)]; omega)) c (by omega), (hinv.strip x h1 h2).1]
      have a15 : x.val - sb d eX pX gW ≠ 15 := by omega
      simp only [slotVal, if_neg a15]
  · intro x h1 h2
    have hk : x = f (x.val - e) := Fin.ext (by rw [fv _ (by omega)]; omega)
    by_cases cS : e + u + 2 ≤ x.val ∧ x.val < e + u + 7
    · obtain ⟨j, hjv⟩ : ∃ j : Fin 9, j.val = x.val - e - u + 1 := ⟨⟨x.val - e - u + 1, by omega⟩, rfl⟩
      have hj : subSl pl hh u j = x := by
        apply Fin.ext
        rw [slv j, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        omega
      rw [← hj]
      exact le_of_eq (l2 j (by omega) (by omega)).symm
    by_cases c0 : x.val = e + u
    · rw [hk, show x.val - e = u by omega]
      rw [f2 _ (by
        intro j h2' h8' hj
        by_cases j2 : j.val = 2
        · rw [show j = 2 from Fin.ext j2, sl2] at hj
          have := congrArg Fin.val hj; rw [vs, fv u (by omega)] at this; omega
        · rw [slj j (by omega)] at hj
          have := congrArg Fin.val hj; rw [fv _ (by omega), fv u (by omega)] at this; omega), hA1,
        Function.update_self]
      exact Uniform.long_pad Rc _
    · rw [keep x (ne_of_val (by rw [fv u (by omega)]; omega)) (by omega) cS, hk,
        (fr (x.val - e) (by omega) (by omega)).1]
      simp

end
end NearCubicWires.SourceSkeleton.InitS
end
