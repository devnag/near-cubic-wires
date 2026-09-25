import Proof.SourceAssembly.SourceSkelInitRes

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

section stages
variable {T : Nat}

theorem ne_of_val {x y : Fin T} (h : x.val ≠ y.val) : x ≠ y := fun e => h (congrArg Fin.val e)

/-- A docked 4-tape stage whose outputs are its slots `2, 3`. -/
theorem dock4_run {s n : Nat} {M : Machine 4 s} (a0 a1 a2 a3 b2 b3 : List Bool)
    (h : Step M n (fun _ => 0) ![a0, a1, a2, a3] (fun _ => 0) ![a0, a1, b2, b3])
    (t0 t1 t2 t3 : Fin T) (h01 : t0.val ≠ t1.val) (h02 : t0.val ≠ t2.val) (h03 : t0.val ≠ t3.val)
    (h12 : t1.val ≠ t2.val) (h13 : t1.val ≠ t3.val) (h23 : t2.val ≠ t3.val)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hH0 : H t0 = 0) (hH1 : H t1 = 0) (hH2 : H t2 = 0) (hH3 : H t3 = 0)
    (hA0 : A t0 = a0) (hA1 : A t1 = a1) (hA2 : A t2 = a2) (hA3 : A t3 = a3) :
    ∃ A', Step (RecoveryFocus.machine (![t0, t1, t2, t3] : Fin 4 → Fin T) M) n H A H A' ∧
      A' t2 = b2 ∧ A' t3 = b3 ∧ ∀ x : Fin T, x ≠ t2 → x ≠ t3 → A' x = A x := by
  have hinj := quad_injective t0 t1 t2 t3 h01 h02 h03 h12 h13 h23
  have st := dockZ h (![t0, t1, t2, t3] : Fin 4 → Fin T) hinj H A
    (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
  refine ⟨_, st, install_slot _ hinj A _ (2 : Fin 4), install_slot _ hinj A _ (3 : Fin 4), ?_⟩
  intro x h2 h3
  by_cases e0 : x = t0
  · rw [e0]; exact (install_slot _ hinj A _ (0 : Fin 4)).trans hA0.symm
  by_cases e1 : x = t1
  · rw [e1]; exact (install_slot _ hinj A _ (1 : Fin 4)).trans hA1.symm
  refine install_other _ A _ x (fun j hj => ?_)
  fin_cases j
  · exact e0 hj.symm
  · exact e1 hj.symm
  · exact h2 hj.symm
  · exact h3 hj.symm

theorem triple_inj (a b c : Fin T) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val) :
    Function.Injective (![a, b, c] : Fin 3 → Fin T) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> simp at hv <;> first | rfl | omega

/-- A docked 3-tape stage whose outputs are its slots `1, 2`. -/
theorem dock3_run {s n : Nat} {M : Machine 3 s} (a0 a1 a2 b1 b2 : List Bool)
    (h : Step M n (fun _ => 0) ![a0, a1, a2] (fun _ => 0) ![a0, b1, b2])
    (t0 t1 t2 : Fin T) (h01 : t0.val ≠ t1.val) (h02 : t0.val ≠ t2.val) (h12 : t1.val ≠ t2.val)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hH0 : H t0 = 0) (hH1 : H t1 = 0) (hH2 : H t2 = 0)
    (hA0 : A t0 = a0) (hA1 : A t1 = a1) (hA2 : A t2 = a2) :
    ∃ A', Step (RecoveryFocus.machine (![t0, t1, t2] : Fin 3 → Fin T) M) n H A H A' ∧
      A' t1 = b1 ∧ A' t2 = b2 ∧ ∀ x : Fin T, x ≠ t1 → x ≠ t2 → A' x = A x := by
  have hinj := triple_inj t0 t1 t2 h01 h02 h12
  have st := dockZ h (![t0, t1, t2] : Fin 3 → Fin T) hinj H A
    (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
  refine ⟨_, st, install_slot _ hinj A _ (1 : Fin 3), install_slot _ hinj A _ (2 : Fin 3), ?_⟩
  intro x h1 h2
  by_cases e0 : x = t0
  · rw [e0]; exact (install_slot _ hinj A _ (0 : Fin 3)).trans hA0.symm
  refine install_other _ A _ x (fun j hj => ?_)
  fin_cases j
  · exact e0 hj.symm
  · exact h1 hj.symm
  · exact h2 hj.symm

theorem pad_nil' (Rc : Nat) : ZeroPadding.pad Rc ([] : List Bool) = List.replicate Rc false :=
  SourceFactorSel.Desc.pad_nil Rc

/-- **`×`, padded.** `V = pad Rc 1^v`, `TP = pad Rc (false :: 1^p)`, blank `Y, Lp`: `Y := pad Rc 1^(v·p)`. -/
theorem prodAt_run (v p Rc : Nat) (V TP Y Lp : Fin T) (h01 : V.val ≠ TP.val) (h02 : V.val ≠ Y.val)
    (h03 : V.val ≠ Lp.val) (h12 : TP.val ≠ Y.val) (h13 : TP.val ≠ Lp.val) (h23 : Y.val ≠ Lp.val)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hH0 : H V = 0) (hH1 : H TP = 0) (hH2 : H Y = 0) (hH3 : H Lp = 0)
    (hA0 : A V = ZeroPadding.pad Rc (List.replicate v true))
    (hA1 : A TP = ZeroPadding.pad Rc (false :: List.replicate p true))
    (hA2 : A Y = List.replicate Rc false) (hA3 : A Lp = List.replicate Rc false) :
    ∃ A', Step (RecoveryFocus.machine (![V, TP, Y, Lp] : Fin 4 → Fin T) ClockUnaryProduct.machine)
        (2*(v*(2*p+3)+2)+2) H A H A' ∧
      A' Y = ZeroPadding.pad Rc (List.replicate (v*p) true) ∧ Rc ≤ (A' Lp).length ∧
      ∀ x : Fin T, x ≠ Y → x ≠ Lp → A' x = A x := by
  have base := (BlockPlatform.UnaryCalc.product_step v p).pad (fun _ => Rc)
  have hin : (fun i => ZeroPadding.pad ((fun _ : Fin (3+1) => Rc) i)
      ((Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
        ![List.replicate v true, false :: List.replicate p true, []] (fun _ : Fin 1 => [])) i)) =
      ![ZeroPadding.pad Rc (List.replicate v true), ZeroPadding.pad Rc (false :: List.replicate p true),
        List.replicate Rc false, List.replicate Rc false] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact pad_nil' Rc
    · exact pad_nil' Rc
  have hout : (fun i => ZeroPadding.pad ((fun _ : Fin (3+1) => Rc) i)
      ((![List.replicate v true, false :: List.replicate p true, List.replicate (v*p) true,
        List.replicate (v*(2*p+3)+2) false] : Fin 4 → List Bool) i)) =
      ![ZeroPadding.pad Rc (List.replicate v true), ZeroPadding.pad Rc (false :: List.replicate p true),
        ZeroPadding.pad Rc (List.replicate (v*p) true), ZeroPadding.pad Rc (List.replicate (v*(2*p+3)+2) false)] := by
    funext i
    fin_cases i <;> rfl
  have st0 := (base.congr_in rfl hin).congr rfl hout
  obtain ⟨A', st, o2, o3, fr⟩ := dock4_run _ _ _ _ _ _ st0 V TP Y Lp h01 h02 h03 h12 h13 h23 H A hH0 hH1 hH2 hH3
    hA0 hA1 hA2 hA3
  refine ⟨A', st, o2, ?_, fr⟩
  rw [o3]; exact Uniform.long_pad Rc _

/-- **`+`, padded.** `R = pad Rc 1^r`, `S' = pad Rc 1^s`, blank `O, Lg`: `O := pad Rc 1^(r+s)`. -/
theorem sumAt_run (r s Rc : Nat) (R S' O Lg : Fin T) (h01 : R.val ≠ S'.val) (h02 : R.val ≠ O.val)
    (h03 : R.val ≠ Lg.val) (h12 : S'.val ≠ O.val) (h13 : S'.val ≠ Lg.val) (h23 : O.val ≠ Lg.val)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hH0 : H R = 0) (hH1 : H S' = 0) (hH2 : H O = 0) (hH3 : H Lg = 0)
    (hA0 : A R = ZeroPadding.pad Rc (List.replicate r true)) (hA1 : A S' = ZeroPadding.pad Rc (List.replicate s true))
    (hA2 : A O = List.replicate Rc false) (hA3 : A Lg = List.replicate Rc false) :
    ∃ A', Step (RecoveryFocus.machine (![R, S', O, Lg] : Fin 4 → Fin T) ClockUnarySum.machine) (2*(r+s)+6) H A H A' ∧
      A' O = ZeroPadding.pad Rc (List.replicate (r+s) true) ∧ Rc ≤ (A' Lg).length ∧
      ∀ x : Fin T, x ≠ O → x ≠ Lg → A' x = A x := by
  have base := (BlockPlatform.UnaryCalc.sum_step r s).pad (fun _ => Rc)
  have hin : (fun i => ZeroPadding.pad ((fun _ : Fin 4 => Rc) i)
      ((![List.replicate r true, List.replicate s true, [], []] : Fin 4 → List Bool) i)) =
      ![ZeroPadding.pad Rc (List.replicate r true), ZeroPadding.pad Rc (List.replicate s true),
        List.replicate Rc false, List.replicate Rc false] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact pad_nil' Rc
    · exact pad_nil' Rc
  have hout : (fun i => ZeroPadding.pad ((fun _ : Fin 4 => Rc) i)
      ((![List.replicate r true, List.replicate s true, List.replicate (r+s) true,
        List.replicate (r+s+2) false] : Fin 4 → List Bool) i)) =
      ![ZeroPadding.pad Rc (List.replicate r true), ZeroPadding.pad Rc (List.replicate s true),
        ZeroPadding.pad Rc (List.replicate (r+s) true), ZeroPadding.pad Rc (List.replicate (r+s+2) false)] := by
    funext i
    fin_cases i <;> rfl
  have st0 := (base.congr_in rfl hin).congr rfl hout
  obtain ⟨A', st, o2, o3, fr⟩ := dock4_run _ _ _ _ _ _ st0 R S' O Lg h01 h02 h03 h12 h13 h23 H A hH0 hH1 hH2 hH3
    hA0 hA1 hA2 hA3
  refine ⟨A', st, o2, ?_, fr⟩
  rw [o3]; exact Uniform.long_pad Rc _

/-- **Copy, padded** (any `r`). `S0 = pad Rc 1^r`, blank `B0, O, Lg`: `O := pad Rc 1^r`. -/
theorem copyPadAt_run (r Rc : Nat) (S0 B0 O Lg : Fin T) (h01 : S0.val ≠ B0.val) (h02 : S0.val ≠ O.val)
    (h03 : S0.val ≠ Lg.val) (h12 : B0.val ≠ O.val) (h13 : B0.val ≠ Lg.val) (h23 : O.val ≠ Lg.val)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hH0 : H S0 = 0) (hH1 : H B0 = 0) (hH2 : H O = 0) (hH3 : H Lg = 0)
    (hA0 : A S0 = ZeroPadding.pad Rc (List.replicate r true)) (hA1 : A B0 = List.replicate Rc false)
    (hA2 : A O = List.replicate Rc false) (hA3 : A Lg = List.replicate Rc false) :
    ∃ A', Step (RecoveryFocus.machine (![S0, B0, O, Lg] : Fin 4 → Fin T) ClockUnarySum.machine) (2*r+6) H A H A' ∧
      A' O = ZeroPadding.pad Rc (List.replicate r true) ∧ Rc ≤ (A' Lg).length ∧
      ∀ x : Fin T, x ≠ O → x ≠ Lg → A' x = A x := by
  have base := (BlockPlatform.UnaryCalc.copy_step r).pad (fun _ => Rc)
  have hin : (fun i => ZeroPadding.pad ((fun _ : Fin 4 => Rc) i)
      ((![List.replicate r true, [], [], []] : Fin 4 → List Bool) i)) =
      ![ZeroPadding.pad Rc (List.replicate r true), List.replicate Rc false,
        List.replicate Rc false, List.replicate Rc false] := by
    funext i
    fin_cases i
    · rfl
    · exact pad_nil' Rc
    · exact pad_nil' Rc
    · exact pad_nil' Rc
  have hout : (fun i => ZeroPadding.pad ((fun _ : Fin 4 => Rc) i)
      ((![List.replicate r true, [], List.replicate r true, List.replicate (r+2) false] : Fin 4 → List Bool) i)) =
      ![ZeroPadding.pad Rc (List.replicate r true), List.replicate Rc false,
        ZeroPadding.pad Rc (List.replicate r true), ZeroPadding.pad Rc (List.replicate (r+2) false)] := by
    funext i
    fin_cases i
    · rfl
    · exact pad_nil' Rc
    · rfl
    · rfl
  have st0 := (base.congr_in rfl hin).congr rfl hout
  obtain ⟨A', st, o2, o3, fr⟩ := dock4_run _ _ _ _ _ _ st0 S0 B0 O Lg h01 h02 h03 h12 h13 h23 H A hH0 hH1 hH2 hH3
    hA0 hA1 hA2 hA3
  refine ⟨A', st, o2, ?_, fr⟩
  rw [o3]; exact Uniform.long_pad Rc _

/-- **Template, padded.** `I = pad Rc 1^p`, blank `O, Lg`: `O := pad Rc (false :: 1^p)` (when `p + 2 ≤ Rc`). -/
theorem tmplAt_run (p Rc : Nat) (hp : p + 2 ≤ Rc) (I O Lg : Fin T) (h01 : I.val ≠ O.val) (h02 : I.val ≠ Lg.val)
    (h12 : O.val ≠ Lg.val) (H : Fin T → ℕ) (A : Fin T → List Bool) (hH0 : H I = 0) (hH1 : H O = 0) (hH2 : H Lg = 0)
    (hA0 : A I = ZeroPadding.pad Rc (List.replicate p true)) (hA1 : A O = List.replicate Rc false)
    (hA2 : A Lg = List.replicate Rc false) :
    ∃ A', Step (RecoveryFocus.machine (![I, O, Lg] : Fin 3 → Fin T) (DimensionTemplate.machine false)) (2*p+8) H A H A' ∧
      A' O = ZeroPadding.pad Rc (false :: List.replicate p true) ∧ Rc ≤ (A' Lg).length ∧
      ∀ x : Fin T, x ≠ O → x ≠ Lg → A' x = A x := by
  have base := Uniform.stepT false p Rc Rc Rc
  have ht : ZeroPadding.pad Rc (UnaryTemplate.tape (p + false.toNat)) =
      ZeroPadding.pad Rc (false :: List.replicate p true) := by
    rw [Bool.toNat_false, Nat.add_zero]
    exact (ExtDecompositionBatch.pad_template Rc p hp).symm
  have st0 := (base.congr_in rfl (by rw [pad_nil'])).congr rfl (by rw [ht])
  obtain ⟨A', st, o1, o2, fr⟩ := dock3_run _ _ _ _ _ st0 I O Lg h01 h02 h12 H A hH0 hH1 hH2 hA0 hA1 hA2
  refine ⟨A', st, o1, ?_, fr⟩
  rw [o2]; exact Uniform.long_pad Rc _

/-! ## Horner's rule -/

/-- One Horner step `v ↦ v·p + a` on the tapes `Y Lp Cw V' Ls` (template `TP`, shared blank word log `LW`). -/
def hStepM (V TP LW Y Lp Cw V' Ls : Fin T) (a : Nat) :=
  Composition.machine (RecoveryFocus.machine (![V, TP, Y, Lp] : Fin 4 → Fin T) ClockUnaryProduct.machine)
    (Composition.machine
      (RecoveryFocus.machine (![Cw, LW] : Fin 2 → Fin T) (HierarchyFixedWord.machine (List.replicate a true)))
      (RecoveryFocus.machine (![Y, Cw, V', Ls] : Fin 4 → Fin T) ClockUnarySum.machine))

def hStepCost (p v a : Nat) : Nat :=
  (2*(v*(2*p+3)+2)+2) + 1 + ((2 * (List.replicate a true).length + 2) + 1 + (2*(v*p+a)+6))

/-- The chain over the coefficient list (step `i` on `f (u+5i) .. f (u+5i+4)`). -/
def hChain (f : Nat → Fin T) (TP LW : Fin T) : List Nat → Fin T → Nat → (Σ s, Machine T s)
  | [], _, _ => ⟨_, CloseoutRowsOriginalSwitch.stop T⟩
  | a :: cs, V, u => ⟨_, Composition.machine (hStepM V TP LW (f u) (f (u+1)) (f (u+2)) (f (u+3)) (f (u+4)) a)
      (hChain f TP LW cs (f (u+3)) (u+5)).2⟩

def hCost (p : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | a :: cs, v => hStepCost p v a + 1 + hCost p cs (v*p + a)

/-- Horner's value. -/
def hVal (p : Nat) : List Nat → Nat → Nat
  | [], v => v
  | a :: cs, v => hVal p cs (v*p + a)

/-- The tape holding the result. -/
def hOut (f : Nat → Fin T) : List Nat → Fin T → Nat → Fin T
  | [], V, _ => V
  | _ :: cs, _, u => hOut f cs (f (u+3)) (u+5)

theorem horner_run (Rc p : Nat) (f : Nat → Fin T) (e : Nat) (TP LW : Fin T) :
    ∀ (cs : List Nat) (v : Nat) (V : Fin T) (u : Nat) (H : Fin T → ℕ) (A : Fin T → List Bool),
    (∀ k, u ≤ k → k < u + 5 * cs.length → (f k).val = e + k) →
    (∀ a, a ∈ cs → a ≤ Rc) →
    (TP.val < e + u ∨ e + u + 5 * cs.length ≤ TP.val) →
    (LW.val < e + u ∨ e + u + 5 * cs.length ≤ LW.val) →
    (V.val < e + u ∨ e + u + 5 * cs.length ≤ V.val) →
    TP.val ≠ LW.val → V.val ≠ TP.val → V.val ≠ LW.val →
    H TP = 0 → H LW = 0 → H V = 0 → (∀ k, u ≤ k → k < u + 5 * cs.length → H (f k) = 0) →
    A TP = ZeroPadding.pad Rc (false :: List.replicate p true) → A LW = List.replicate Rc false →
    A V = ZeroPadding.pad Rc (List.replicate v true) →
    (∀ k, u ≤ k → k < u + 5 * cs.length → A (f k) = List.replicate Rc false) →
    ∃ A', Step (hChain f TP LW cs V u).2 (hCost p cs v) H A H A' ∧
      A' (hOut f cs V u) = ZeroPadding.pad Rc (List.replicate (hVal p cs v) true) ∧
      (∀ k, u ≤ k → k < u + 5 * cs.length → Rc ≤ (A' (f k)).length) ∧
      (∀ x : Fin T, ¬ (e + u ≤ x.val ∧ x.val < e + u + 5 * cs.length) → A' x = A x) := by
  intro cs
  induction cs with
  | nil =>
    intro v V u H A _ _ _ _ _ _ _ _ _ _ _ _ _ _ hV _
    refine ⟨A, SourceConstruction.stop_step H A, hV, fun k h1 h2 => by simp at h2; omega, fun _ _ => rfl⟩
  | cons a cs ih =>
    intro v V u H A hf ha hTP hLW hVo hTL hVT hVL hHT hHL hHV hHb hAT hAL hAV hAb
    have hl : (a :: cs).length = cs.length + 1 := rfl
    rw [hl] at hf hTP hLW hVo hHb hAb
    have v0 : (f u).val = e + u := hf u le_rfl (by omega)
    have v1 : (f (u+1)).val = e + (u+1) := hf (u+1) (by omega) (by omega)
    have v2 : (f (u+2)).val = e + (u+2) := hf (u+2) (by omega) (by omega)
    have v3 : (f (u+3)).val = e + (u+3) := hf (u+3) (by omega) (by omega)
    have v4 : (f (u+4)).val = e + (u+4) := hf (u+4) (by omega) (by omega)
    have haR : a ≤ Rc := ha a (List.mem_cons_self)
    -- the product `v·p` onto `f u` (log `f (u+1)`)
    obtain ⟨A1, s1, oY, oLp, f1⟩ := prodAt_run v p Rc V TP (f u) (f (u+1)) (by omega) (by rw [v0]; omega)
      (by rw [v1]; omega) (by rw [v0]; omega) (by rw [v1]; omega) (by rw [v0, v1]; omega) H A hHV hHT
      (hHb u le_rfl (by omega)) (hHb (u+1) (by omega) (by omega)) hAV hAT (hAb u le_rfl (by omega))
      (hAb (u+1) (by omega) (by omega))
    -- the constant `1^a` onto `f (u+2)` (log `LW`)
    have c2 : A1 (f (u+2)) = List.replicate Rc false := by
      rw [f1 _ (ne_of_val (by rw [v2, v0]; omega)) (ne_of_val (by rw [v2, v1]; omega))]
      exact hAb (u+2) (by omega) (by omega)
    have cLW : A1 LW = List.replicate Rc false := by
      rw [f1 _ (ne_of_val (by rw [v0]; omega)) (ne_of_val (by rw [v1]; omega))]; exact hAL
    have s2 := word_step (List.replicate a true) (f (u+2)) LW (ne_of_val (by rw [v2]; omega)) Rc Rc
      (by rw [List.length_replicate]; exact haR) H A1 (hHb (u+2) (by omega) (by omega)) hHL c2 cLW
    set A2 := Function.update A1 (f (u+2)) (ZeroPadding.pad Rc (List.replicate a true)) with hA2
    have up : ∀ x : Fin T, x ≠ f (u+2) → A2 x = A1 x := fun x hx => Function.update_of_ne hx _ _
    -- the sum onto `f (u+3)` (log `f (u+4)`)
    obtain ⟨A3, s3, oV, oLs, f3⟩ := sumAt_run (v*p) a Rc (f u) (f (u+2)) (f (u+3)) (f (u+4))
      (by rw [v0, v2]; omega) (by rw [v0, v3]; omega) (by rw [v0, v4]; omega) (by rw [v2, v3]; omega)
      (by rw [v2, v4]; omega) (by rw [v3, v4]; omega) H A2 (hHb u le_rfl (by omega)) (hHb (u+2) (by omega) (by omega))
      (hHb (u+3) (by omega) (by omega)) (hHb (u+4) (by omega) (by omega))
      (by rw [up _ (ne_of_val (by rw [v0, v2]; omega))]; exact oY) (Function.update_self _ _ _)
      (by rw [up _ (ne_of_val (by rw [v3, v2]; omega)), f1 _ (ne_of_val (by rw [v3, v0]; omega))
            (ne_of_val (by rw [v3, v1]; omega))]; exact hAb (u+3) (by omega) (by omega))
      (by rw [up _ (ne_of_val (by rw [v4, v2]; omega)), f1 _ (ne_of_val (by rw [v4, v0]; omega))
            (ne_of_val (by rw [v4, v1]; omega))]; exact hAb (u+4) (by omega) (by omega))
    -- everything off the step's five tapes is as before
    have keep : ∀ x : Fin T, ¬ (e + u ≤ x.val ∧ x.val < e + u + 5) → A3 x = A x := by
      intro x hx
      rw [f3 x (ne_of_val (by rw [v3]; omega)) (ne_of_val (by rw [v4]; omega)),
        up x (ne_of_val (by rw [v2]; omega)), f1 x (ne_of_val (by rw [v0]; omega)) (ne_of_val (by rw [v1]; omega))]
    -- the rest of the chain
    obtain ⟨A4, s4, o4, l4, fr4⟩ := ih (v*p + a) (f (u+3)) (u+5) H A3
      (fun k h1 h2 => hf k (by omega) (by omega)) (fun b hb => ha b (List.mem_cons_of_mem a hb))
      (by omega) (by omega) (by rw [v3]; omega) hTL (by rw [v3]; omega) (by rw [v3]; omega) hHT hHL
      (hHb (u+3) (by omega) (by omega)) (fun k h1 h2 => hHb k (by omega) (by omega))
      (by rw [keep TP (by omega)]; exact hAT) (by rw [keep LW (by omega)]; exact hAL) oV
      (fun k h1 h2 => by
        rw [keep (f k) (by rw [hf k (by omega) (by omega)]; omega)]
        exact hAb k (by omega) (by omega))
    refine ⟨A4, (s1.seq (s2.seq s3)).seq s4, o4, ?_, ?_⟩
    · intro k h1 h2
      by_cases hk : k < u + 5
      · have vk := hf k h1 (by omega)
        rw [fr4 (f k) (by rw [vk]; omega)]
        by_cases k0 : k = u
        · subst k0
          rw [f3 _ (ne_of_val (by rw [v0, v3]; omega)) (ne_of_val (by rw [v0, v4]; omega)),
            up _ (ne_of_val (by rw [v0, v2]; omega)), oY]
          exact Uniform.long_pad Rc _
        by_cases k1 : k = u + 1
        · subst k1
          rw [f3 _ (ne_of_val (by rw [v1, v3]; omega)) (ne_of_val (by rw [v1, v4]; omega)),
            up _ (ne_of_val (by rw [v1, v2]; omega))]
          exact oLp
        by_cases k2 : k = u + 2
        · subst k2
          rw [f3 _ (ne_of_val (by rw [v2, v3]; omega)) (ne_of_val (by rw [v2, v4]; omega)), hA2,
            Function.update_self]
          exact Uniform.long_pad Rc _
        by_cases k3 : k = u + 3
        · subst k3
          rw [oV]; exact Uniform.long_pad Rc _
        · have k4 : k = u + 4 := by omega
          subst k4
          exact oLs
      · exact l4 k (by omega) (by omega)
    · intro x hx
      rw [fr4 x (by omega), keep x (by omega)]

end stages

end
end NearCubicWires.SourceSkeleton.InitS
end
