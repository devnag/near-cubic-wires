import Proof.SourceAssembly.SourceSkelInitAll

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

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-! ## 1. `hrG 5 = pad Rc (1^b)` -/

/-- Copy `rsT 3 = pad Rc 1^b` onto strip slot 19 (blank `u`, log `u+1`). -/
def bM (u : Nat) :=
  RecoveryFocus.machine (![Dims.rsT pl.ext.rest pl.hT 3, extF (NS := NS) pl u, stripT pl hh 19 (by decide),
    extF (NS := NS) pl (u+1)] : Fin 4 → Fin T) ClockUnarySum.machine

theorem b_step {NR NE : Nat} (hNR20 : 20 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} (hu : u + 2 ≤ NE) {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hinv : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (h19 : val 19 = none) :
    ∃ A'', Step (bM pl hh u) (2*b+6) H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun j => if j = 19 then some (ZeroPadding.pad Rc (List.replicate b true)) else val j)
        (u + 2) H A H' A'' := by
  obtain ⟨hF0, hB0, h11', h12', hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  have v3 : (Dims.rsT pl.ext.rest pl.hT 3).val = d.B + 19 + restPc eX pX gW + 3 := rfl
  have vs : ∀ j hj, (stripT pl hh j hj).val = sb d eX pX gW + j := fun _ _ => rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  set f := extF (NS := NS) pl with hfd
  set e := eb d eX pX gW X NS with hed
  have fv : ∀ k, k < NE → (f k).val = e + k := fun k hk => extF_val pl hE k hk
  have fr : ∀ k, u ≤ k → k < NE → A' (f k) = List.replicate Rc false ∧ H' (f k) = 0 := fun k h1 h2 =>
    hinv.fresh (f k) (by rw [fv k h2]; omega) (by rw [fv k h2]; omega)
  have d19 : A' (stripT pl hh 19 (by decide)) = List.replicate Rc false ∧ H' (stripT pl hh 19 (by decide)) = 0 := by
    have := hinv.strip (stripT pl hh 19 (by decide)) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + 19 - sb d eX pX gW = 19 by omega, slotVal_none Rc val 19 h19] at this
    exact this
  have r3 : A' (Dims.rsT pl.ext.rest pl.hT 3) = ZeroPadding.pad Rc (List.replicate b true) ∧
      H' (Dims.rsT pl.ext.rest pl.hT 3) = 0 := by
    obtain ⟨H1, A1, ho, hag⟩ := hinv.base
    have e3 := hag (Dims.rsT pl.ext.rest pl.hT 3) (by rw [v3]; omega) (by rw [v3]; unfold eb at *; omega)
    rw [e3.1, e3.2]; exact ho.wres
  obtain ⟨A1, s1, o1, l1, f1⟩ := copyPadAt_run b Rc (Dims.rsT pl.ext.rest pl.hT 3) (f u) (stripT pl hh 19 (by decide))
    (f (u+1)) (by rw [v3, fv u (by omega)]; unfold eb at *; omega) (by rw [v3, vs]; omega)
    (by rw [v3, fv (u+1) (by omega)]; unfold eb at *; omega) (by rw [fv u (by omega), vs]; omega)
    (by rw [fv u (by omega), fv (u+1) (by omega)]; omega) (by rw [vs, fv (u+1) (by omega)]; omega)
    H' A' r3.2 (fr u le_rfl (by omega)).2 d19.2 (fr (u+1) (by omega) (by omega)).2
    r3.1 (fr u le_rfl (by omega)).1 d19.1 (fr (u+1) (by omega) (by omega)).1
  refine ⟨A1, s1, step pl hh hNR hinv A1 _ (u + 2) (by omega) hu ?_ ?_ ?_⟩
  · intro x h1 h2
    exact f1 x (ne_of_val (by rw [vs]; omega)) (ne_of_val (by rw [fv (u+1) (by omega)]; omega))
  · intro x h1 h2
    by_cases c : x.val = sb d eX pX gW + 19
    · have ex : x = stripT pl hh 19 (by decide) := Fin.ext (by rw [vs]; exact c)
      rw [ex, o1, vs, show sb d eX pX gW + 19 - sb d eX pX gW = 19 by omega]
      simp [slotVal]
    · rw [f1 x (fun h => c (by rw [h, vs])) (ne_of_val (by rw [fv (u+1) (by omega)]; omega)), (hinv.strip x h1 h2).1]
      have a19 : x.val - sb d eX pX gW ≠ 19 := by omega
      simp only [slotVal, if_neg a19]
  · intro x h1 h2
    have hk : x = f (x.val - e) := Fin.ext (by rw [fv _ (by omega)]; omega)
    by_cases c1 : x.val = e + u + 1
    · rw [hk, show x.val - e = u + 1 by omega]; exact l1
    · rw [f1 x (ne_of_val (by rw [vs]; omega)) (ne_of_val (by rw [fv (u+1) (by omega)]; omega)), hk,
        (fr (x.val - e) (by omega) (by omega)).1]
      simp

/-! ## 2. `hrG 2 = pad Rc (tape K)` -/

/-- The fixed word `tape 2` onto `u` (log `u+1`); `hrG 1 / 2` onto `u+2` (log `u+3`); the template of `u+2` onto strip slot 16 (log `u+4`). -/
def tkM (u : Nat) :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine (![extF (NS := NS) pl u, extF (NS := NS) pl (u+1)] : Fin 2 → Fin T)
      (HierarchyFixedWord.machine (UnaryTemplate.tape 2)))
    (RecoveryFocus.machine (![stripT pl hh 15 (by decide), extF (NS := NS) pl u, extF (NS := NS) pl (u+2),
      extF (NS := NS) pl (u+3)] : Fin 4 → Fin T) MatrixBucketDivide.machine))
    (RecoveryFocus.machine (![extF (NS := NS) pl (u+2), stripT pl hh 16 (by decide), extF (NS := NS) pl (u+4)] : Fin 3 → Fin T)
      (DimensionTemplate.machine false))

/-- The cost of `tkM`. -/
def tkCost (K : Nat) : Nat := (2 * (UnaryTemplate.tape 2).length + 2) + 1 + (8*(2*K)+6) + 1 + (2*K+8)

theorem tk_step {NR NE : Nat} (hNR17 : 17 ≤ NR) (hNR : NR ≤ 32) (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    {val : Nat → Option (List Bool)} {u : Nat} (hu : u + 5 ≤ NE) {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hinv : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A')
    (h15 : val 15 = some (ZeroPadding.pad Rc (frame (List.replicate (normalizedLiveCount q L) true))))
    (h16 : val 16 = none) (hK : 2 * normalizedLiveCount q L + 4 ≤ Rc) :
    ∃ A'', Step (tkM pl hh u) (tkCost (normalizedLiveCount q L)) H' A' H' A'' ∧
      InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg
        (fun j => if j = 16 then some (ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L))) else val j)
        (u + 5) H A H' A'' := by
  obtain ⟨hF0, hB0, h11', h12', hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  have vs : ∀ j hj, (stripT pl hh j hj).val = sb d eX pX gW + j := fun _ _ => rfl
  set K := normalizedLiveCount q L with hKd
  set f := extF (NS := NS) pl with hfd
  set e := eb d eX pX gW X NS with hed
  have fv : ∀ k, k < NE → (f k).val = e + k := fun k hk => extF_val pl hE k hk
  have fr : ∀ k, u ≤ k → k < NE → A' (f k) = List.replicate Rc false ∧ H' (f k) = 0 := fun k h1 h2 =>
    hinv.fresh (f k) (by rw [fv k h2]; omega) (by rw [fv k h2]; omega)
  have a15 : A' (stripT pl hh 15 (by decide)) = ZeroPadding.pad Rc (List.replicate (2*K) true) ∧
      H' (stripT pl hh 15 (by decide)) = 0 := by
    have := hinv.strip (stripT pl hh 15 (by decide)) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + 15 - sb d eX pX gW = 15 by omega, slotVal_some Rc val 15 _ h15,
      pad_frame_ones Rc K (by omega)] at this
    exact this
  have d16 : A' (stripT pl hh 16 (by decide)) = List.replicate Rc false ∧ H' (stripT pl hh 16 (by decide)) = 0 := by
    have := hinv.strip (stripT pl hh 16 (by decide)) (by rw [vs]; omega) (by rw [vs]; omega)
    rw [vs, show sb d eX pX gW + 16 - sb d eX pX gW = 16 by omega, slotVal_none Rc val 16 h16] at this
    exact this
  -- the divisor `tape 2`
  have s1 := word_step (UnaryTemplate.tape 2) (f u) (f (u+1))
    (ne_of_val (by rw [fv u (by omega), fv (u+1) (by omega)]; omega)) Rc Rc
    (by show 4 ≤ Rc; omega) H' A' (fr u le_rfl (by omega)).2 (fr (u+1) (by omega) (by omega)).2
    (fr u le_rfl (by omega)).1 (fr (u+1) (by omega) (by omega)).1
  set A1 := Function.update A' (f u) (ZeroPadding.pad Rc (UnaryTemplate.tape 2)) with hA1
  have up : ∀ x : Fin T, x ≠ f u → A1 x = A' x := fun x hx => Function.update_of_ne hx _ _
  -- the division `1^(2K) / 2 = 1^K`
  obtain ⟨W, sW, w0, w1, w2, wl⟩ := InitSlopes.stepDiv (2*K) 2 Rc (by decide)
  have eW : W = ![ZeroPadding.pad Rc (List.replicate (2*K) true), ZeroPadding.pad Rc (UnaryTemplate.tape 2), W 2, W 3] := by
    funext i; fin_cases i
    · exact w0
    · exact w1
    · rfl
    · rfl
  have sW' : Step MatrixBucketDivide.machine (8*(2*K)+6) (fun _ => 0)
      ![ZeroPadding.pad Rc (List.replicate (2*K) true), ZeroPadding.pad Rc (UnaryTemplate.tape 2),
        ZeroPadding.pad Rc [], ZeroPadding.pad Rc []] (fun _ => 0)
      ![ZeroPadding.pad Rc (List.replicate (2*K) true), ZeroPadding.pad Rc (UnaryTemplate.tape 2), W 2, W 3] := by
    rw [← eW]; exact sW
  obtain ⟨A2, s2, o2, o3, f2⟩ := dock4_run _ _ _ _ _ _ sW' (stripT pl hh 15 (by decide)) (f u) (f (u+2)) (f (u+3))
    (by rw [vs, fv u (by omega)]; omega) (by rw [vs, fv (u+2) (by omega)]; omega) (by rw [vs, fv (u+3) (by omega)]; omega)
    (by rw [fv u (by omega), fv (u+2) (by omega)]; omega) (by rw [fv u (by omega), fv (u+3) (by omega)]; omega)
    (by rw [fv (u+2) (by omega), fv (u+3) (by omega)]; omega)
    H' A1 a15.2 (fr u le_rfl (by omega)).2 (fr (u+2) (by omega) (by omega)).2 (fr (u+3) (by omega) (by omega)).2
    (by rw [up _ (ne_of_val (by rw [vs, fv u (by omega)]; omega))]; exact a15.1)
    (by rw [hA1, Function.update_self])
    (by rw [up _ (ne_of_val (by rw [fv (u+2) (by omega), fv u (by omega)]; omega)), (fr (u+2) (by omega) (by omega)).1,
          pad_nil'])
    (by rw [up _ (ne_of_val (by rw [fv (u+3) (by omega), fv u (by omega)]; omega)), (fr (u+3) (by omega) (by omega)).1,
          pad_nil'])
  have hdiv : 2*K/2 = K := by omega
  rw [w2, hdiv] at o2
  -- the template `pad Rc (false :: 1^K)` onto strip slot 16
  obtain ⟨A3, s3, o4, l4, f4⟩ := tmplAt_run K Rc (by omega) (f (u+2)) (stripT pl hh 16 (by decide)) (f (u+4))
    (by rw [fv (u+2) (by omega), vs]; omega) (by rw [fv (u+2) (by omega), fv (u+4) (by omega)]; omega)
    (by rw [vs, fv (u+4) (by omega)]; omega) H' A2
    (fr (u+2) (by omega) (by omega)).2 d16.2 (fr (u+4) (by omega) (by omega)).2 o2
    (by rw [f2 _ (ne_of_val (by rw [vs, fv (u+2) (by omega)]; omega)) (ne_of_val (by rw [vs, fv (u+3) (by omega)]; omega)),
          up _ (ne_of_val (by rw [vs, fv u (by omega)]; omega))]; exact d16.1)
    (by rw [f2 _ (ne_of_val (by rw [fv (u+4) (by omega), fv (u+2) (by omega)]; omega))
          (ne_of_val (by rw [fv (u+4) (by omega), fv (u+3) (by omega)]; omega)),
          up _ (ne_of_val (by rw [fv (u+4) (by omega), fv u (by omega)]; omega))]
        exact (fr (u+4) (by omega) (by omega)).1)
  have htk : ZeroPadding.pad Rc (false :: List.replicate K true) = ZeroPadding.pad Rc (UnaryTemplate.tape K) :=
    ExtDecompositionBatch.pad_template Rc K (by omega)
  -- a tape off the stage's changed set: unchanged
  have keep : ∀ x : Fin T, x ≠ f u → x.val ≠ sb d eX pX gW + 16 →
      ¬ (e + u + 2 ≤ x.val ∧ x.val < e + u + 5) → A3 x = A' x := by
    intro x hxu hx16 hx
    rw [f4 x (fun h => hx16 (by rw [h, vs])) (fun h => hx ⟨by rw [h, fv (u+4) (by omega)]; omega, by rw [h, fv (u+4) (by omega)]; omega⟩),
      f2 x (fun h => hx ⟨by rw [h, fv (u+2) (by omega)]; omega, by rw [h, fv (u+2) (by omega)]; omega⟩)
        (fun h => hx ⟨by rw [h, fv (u+3) (by omega)]; omega, by rw [h, fv (u+3) (by omega)]; omega⟩)]
    exact up x hxu
  refine ⟨A3, (s1.seq s2).seq s3, step pl hh hNR hinv A3 _ (u + 5) (by omega) hu ?_ ?_ ?_⟩
  · intro x h1 h2
    exact keep x (ne_of_val (by rw [fv u (by omega)]; omega)) (by omega) (by omega)
  · intro x h1 h2
    by_cases c : x.val = sb d eX pX gW + 16
    · have ex : x = stripT pl hh 16 (by decide) := Fin.ext (by rw [vs]; exact c)
      rw [ex, o4, htk, vs, show sb d eX pX gW + 16 - sb d eX pX gW = 16 by omega]
      simp [slotVal]
    · rw [keep x (ne_of_val (by rw [fv u (by omega)]; omega)) c (by omega), (hinv.strip x h1 h2).1]
      have a16 : x.val - sb d eX pX gW ≠ 16 := by omega
      simp only [slotVal, if_neg a16]
  · intro x h1 h2
    have hk : x = f (x.val - e) := Fin.ext (by rw [fv _ (by omega)]; omega)
    by_cases c4 : x.val = e + u + 4
    · rw [hk, show x.val - e = u + 4 by omega]; exact l4
    have n4 : x ≠ f (u+4) := ne_of_val (by rw [fv (u+4) (by omega)]; omega)
    have n16 : x ≠ stripT pl hh 16 (by decide) := ne_of_val (by rw [vs]; omega)
    rw [f4 x n16 n4]
    by_cases c3 : x.val = e + u + 3
    · rw [hk, show x.val - e = u + 3 by omega, o3]; exact wl 3
    by_cases c2 : x.val = e + u + 2
    · rw [hk, show x.val - e = u + 2 by omega, o2]; exact Uniform.long_pad Rc _
    have n2 : x ≠ f (u+2) := ne_of_val (by rw [fv (u+2) (by omega)]; omega)
    have n3 : x ≠ f (u+3) := ne_of_val (by rw [fv (u+3) (by omega)]; omega)
    rw [f2 x n2 n3]
    by_cases c0 : x.val = e + u
    · rw [hk, show x.val - e = u by omega, hA1, Function.update_self]; exact Uniform.long_pad Rc _
    · rw [up x (ne_of_val (by rw [fv u (by omega)]; omega)), hk, (fr (x.val - e) (by omega) (by omega)).1]
      simp

end
end NearCubicWires.SourceSkeleton.InitS
end

