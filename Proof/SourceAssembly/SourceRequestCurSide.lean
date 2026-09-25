import Proof.SourceAssembly.SourceRequestCurWriter

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CurSide
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp NearCubicWires.SourceRequest.CurWriter
open NearCubicWires.SourceFactorSel.Count (mulM wordM mul_step word0_step read_flag)
noncomputable section

/-! ## Generic helpers: length bookkeeping, interval frames, the `CursorOut` builder -/

/-- Every tape is either untouched or of length `≤ S`. -/
def LenOK (S : Nat) (A A' : Fin 128 → List Bool) : Prop := ∀ z, A' z = A z ∨ (A' z).length ≤ S

theorem LenOK.refl (S : Nat) (A : Fin 128 → List Bool) : LenOK S A A := fun _ => Or.inl rfl

theorem LenOK.trans {S : Nat} {A B C : Fin 128 → List Bool} (h1 : LenOK S A B) (h2 : LenOK S B C) :
    LenOK S A C := by
  intro z
  rcases h2 z with e | e
  · rcases h1 z with e' | e'
    · exact Or.inl (e.trans e')
    · exact Or.inr (e ▸ e')
  · exact Or.inr e

theorem LenOK.update {S : Nat} (A : Fin 128 → List Bool) (d : Fin 128) (w : List Bool) (hw : w.length ≤ S) :
    LenOK S A (Function.update A d (ZeroPadding.pad S w)) := by
  intro z
  by_cases e : z = d
  · subst e; right; rw [Function.update_self, pad_len S w hw]
  · left; exact Function.update_of_ne e _ _

theorem LenOK.chain {S : Nat} (ws : List Wr) (A : Fin 128 → List Bool) (hw : ∀ x ∈ ws, (x.out S).length ≤ S) :
    LenOK S A (chainApp S ws A) := by
  induction ws generalizing A with
  | nil => exact LenOK.refl S A
  | cons x xs ih =>
    refine LenOK.trans ?_ (ih (x.app S A) (fun y hy => hw y (List.mem_cons_of_mem x hy)))
    intro z
    unfold Wr.app
    by_cases e : z = x.dst
    · subst e; right; rw [Function.update_self]; exact hw x List.mem_cons_self
    · left; exact Function.update_of_ne e _ _

/-- The block test, interval frame. -/
theorem testI (sl : Fin 5 → Fin 128) (hsl : Function.Injective sl) (lo hi : Nat)
    (hfp : lo ≤ (sl 2).val ∧ (sl 2).val < hi ∧ lo ≤ (sl 3).val ∧ (sl 3).val < hi)
    (s x Qa Qb S C : Nat) (hS : s + 2 ≤ S) (hC : s + 3 ≤ C) (A : Fin 128 → List Bool)
    (h0 : A (sl 0) = ZeroPadding.pad Qa (List.replicate s true))
    (h1 : A (sl 1) = ZeroPadding.pad Qb (List.replicate x true))
    (h2 : A (sl 2) = List.replicate S false) (h3 : A (sl 3) = List.replicate S false)
    (h4 : A (sl 4) = List.replicate C false) :
    ∃ A' : Fin 128 → List Bool, Step (testM sl) (testCost s) (fun _ => 0) A (fun _ => 0) A' ∧
      A' (sl 2) = ZeroPadding.pad S [decide (s ≤ x)] ∧
      (∀ z : Fin 128, z.val < lo ∨ hi ≤ z.val → A' z = A z) ∧ LenOK S A A' := by
  obtain ⟨A', st, a2, fr, l3⟩ := test_step sl hsl s x Qa Qb S C hS hC (fun _ => 0) A (fun _ => rfl) h0 h1 h2 h3 h4
  refine ⟨A', st, a2, ?_, ?_⟩
  · intro z hz
    exact fr z (fun e => by rw [← e] at hz; omega) (fun e => by rw [← e] at hz; omega)
  · intro z
    by_cases e2 : sl 2 = z
    · subst e2; right; rw [a2, pad_len S _ (by simp; omega)]
    · by_cases e3 : sl 3 = z
      · subst e3; right; exact le_of_eq l3
      · left; exact fr z e2 e3

/-- `x - y`, interval frame. -/
theorem subI (sl : Fin 9 → Fin 128) (hsl : Function.Injective sl) (lo hi : Nat)
    (hfp : ∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → lo ≤ (sl j).val ∧ (sl j).val < hi)
    (x y Qa Qb S C : Nat) (hy : y ≤ x) (hS : x + 2 ≤ S) (hC : 2 * x + 5 ≤ C) (A : Fin 128 → List Bool)
    (h0 : A (sl 0) = ZeroPadding.pad Qa (List.replicate x true))
    (h1 : A (sl 1) = ZeroPadding.pad Qb (List.replicate y true))
    (hscr : ∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → A (sl j) = List.replicate S false)
    (h8 : A (sl 8) = List.replicate C false) :
    ∃ A' : Fin 128 → List Bool, Step (subM sl) (subCost x) (fun _ => 0) A (fun _ => 0) A' ∧
      A' (sl 2) = ZeroPadding.pad S (List.replicate (x - y) true) ∧
      (∀ z : Fin 128, z.val < lo ∨ hi ≤ z.val → A' z = A z) ∧ LenOK S A A' := by
  obtain ⟨A', st, a2, fr, ll⟩ := sub_step sl hsl x y Qa Qb S C hy hS hC (fun _ => 0) A (fun _ => rfl) h0 h1 hscr h8
  refine ⟨A', st, a2, ?_, ?_⟩
  · intro z hz
    exact fr z (fun j h2 h8 e => by have := hfp j h2 h8; rw [e] at this; omega)
  · intro z
    by_cases hp : ∃ j : Fin 9, 2 ≤ j.val ∧ j.val < 8 ∧ sl j = z
    · obtain ⟨j, h2, h8, rfl⟩ := hp
      right; exact le_of_eq (ll j h2 h8)
    · left; exact fr z (fun j h2 h8 e => hp ⟨j, h2, h8, e⟩)

/-- `x / J`, `x % J`, interval frame. -/
theorem divI (sl : Fin 11 → Fin 128) (hsl : Function.Injective sl) (lo hi : Nat)
    (hfp : ∀ j : Fin 11, 2 ≤ j.val → j.val < 10 → lo ≤ (sl j).val ∧ (sl j).val < hi)
    (x J Qa Qb S C : Nat) (hJ : 0 < J) (hQb : J + 2 ≤ Qb) (hS : x + 2 ≤ S) (hC : 5 * x + 5 ≤ C)
    (A : Fin 128 → List Bool)
    (h0 : A (sl 0) = ZeroPadding.pad Qa (List.replicate x true))
    (h1 : A (sl 1) = ZeroPadding.pad Qb (CompareMachine.word J))
    (hscr : ∀ j : Fin 11, 2 ≤ j.val → j.val < 10 → A (sl j) = List.replicate S false)
    (h10 : A (sl 10) = List.replicate C false) :
    ∃ A' : Fin 128 → List Bool, Step (divmodM sl) (divmodCost x) (fun _ => 0) A (fun _ => 0) A' ∧
      A' (sl 2) = ZeroPadding.pad S (List.replicate (x / J) true) ∧
      A' (sl 3) = ZeroPadding.pad S (List.replicate (x % J) true) ∧
      (∀ z : Fin 128, z.val < lo ∨ hi ≤ z.val → A' z = A z) ∧ LenOK S A A' := by
  obtain ⟨A', st, a2, a3, fr, ll⟩ :=
    divmod_step sl hsl x J Qa Qb S C hJ hQb hS hC (fun _ => 0) A (fun _ => rfl) h0 h1 hscr h10
  refine ⟨A', st, a2, a3, ?_, ?_⟩
  · intro z hz
    exact fr z (fun j h2 h10 e => by have := hfp j h2 h10; rw [e] at this; omega)
  · intro z
    by_cases hp : ∃ j : Fin 11, 2 ≤ j.val ∧ j.val < 10 ∧ sl j = z
    · obtain ⟨j, h2, h10, rfl⟩ := hp
      right; exact le_of_eq (ll j h2 h10)
    · left; exact fr z (fun j h2 h10 e => hp ⟨j, h2, h10, e⟩)

/-- `CursorOut` from its eighteen port equations, stated at the numeric ports. -/
theorem cursorOut_of (σ : Option Sel) (S : Nat) (E : Fin 128 → List Bool)
    (s0 : E 6 = ZeroPadding.pad S [fSys (facAt σ 0)]) (s1 : E 10 = ZeroPadding.pad S [fSys (facAt σ 1)])
    (s2 : E 14 = ZeroPadding.pad S [fSys (facAt σ 2)]) (s3 : E 18 = ZeroPadding.pad S [fSys (facAt σ 3)])
    (t0 : E 7 = ZeroPadding.pad S [fTerm (facAt σ 0)]) (t1 : E 11 = ZeroPadding.pad S [fTerm (facAt σ 1)])
    (t2 : E 15 = ZeroPadding.pad S [fTerm (facAt σ 2)]) (t3 : E 19 = ZeroPadding.pad S [fTerm (facAt σ 3)])
    (r0 : E 8 = ZeroPadding.pad S [fSide (facAt σ 0)]) (r1 : E 12 = ZeroPadding.pad S [fSide (facAt σ 1)])
    (r2 : E 16 = ZeroPadding.pad S [fSide (facAt σ 2)]) (r3 : E 20 = ZeroPadding.pad S [fSide (facAt σ 3)])
    (i0 : E 9 = ZeroPadding.pad S (List.replicate (fIdx (facAt σ 0)) true))
    (i1 : E 13 = ZeroPadding.pad S (List.replicate (fIdx (facAt σ 1)) true))
    (i2 : E 17 = ZeroPadding.pad S (List.replicate (fIdx (facAt σ 2)) true))
    (i3 : E 21 = ZeroPadding.pad S (List.replicate (fIdx (facAt σ 3)) true))
    (k : E 22 = ZeroPadding.pad S (List.replicate (kOf σ) true))
    (rh : E 23 = ZeroPadding.pad S (CloseoutRowsEstimatorCoefficients.Product.record rhoW (rhoOf σ))) :
    CursorOut σ S E :=
  ⟨forall4 s0 s1 s2 s3, forall4 t0 t1 t2 t3, forall4 r0 r1 r2 r3, forall4 i0 i1 i2 i3, k, rh⟩

theorem ex_pad (S : Nat) (w : List Bool) : (∃ Qa, ZeroPadding.pad S w = ZeroPadding.pad Qa w) = True :=
  eq_true ⟨S, rfl⟩

theorem pad_nil' (S : Nat) : ZeroPadding.pad S [] = List.replicate S false := by simp [ZeroPadding.pad]

theorem rec_len (q : ℚ) : (CloseoutRowsEstimatorCoefficients.Product.record rhoW q).length = 13 := by
  rw [record_len]; rfl

/-! ## The side contract -/

/-- **One penalty side's decode at a fixed machine** (side `r` fixed by the machine; `s` read from port `3`). -/
def SideRun {st : Nat} (M : Machine 128 st) (r : Bool) : Prop :=
  ∀ (s : Bool) (x J Qx QJ Qf S C : Nat) (E : Fin 128 → List Bool),
    x < MonomialSpec.penLen s J → curBig J 0 ≤ S → curBig J 0 ≤ C →
    E 0 = ZeroPadding.pad Qx (List.replicate x true) → E 1 = ZeroPadding.pad QJ (List.replicate J true) →
    E 3 = ZeroPadding.pad Qf [!s] → E 5 = List.replicate C false →
    (∀ j : Fin 128, 6 ≤ j.val → j.val < 80 → E j = List.replicate S false) →
    ∃ E' : Fin 128 → List Bool, Step M (16 * curBig J 0) (fun _ => 0) E (fun _ => 0) E' ∧
      CursorOut (((penSide s r J)[x]?).map halfSel) S E' ∧
      (∀ j : Fin 128, j.val < 6 ∨ 80 ≤ j.val → E' j = E j) ∧ LenOK S E E'

/-! ## The systematic side (`s = true`) -/

def sys0W (r : Bool) : List Wr :=
  [.c 6 [true], .c 8 [r], .c 22 [true], .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (1 / 2))]
def sys1W (r : Bool) (y : Nat) : List Wr :=
  [.c 6 [true], .c 8 [r], .cp 27 13 y, .c 11 [true], .c 12 [r], .c 22 [true, true],
    .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (-1))]
def sys2W (r : Bool) (q u : Nat) : List Wr :=
  [.cp 42 9 q, .cp 43 13 u, .c 7 [true], .c 8 [r], .c 11 [true], .c 12 [r], .c 22 [true, true],
    .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (1 / 2))]

def t25 : Fin 5 → Fin 128 := ![24, 0, 25, 26, 5]
def s27 : Fin 9 → Fin 128 := ![0, 24, 27, 28, 29, 30, 31, 32, 5]
def t33 : Fin 5 → Fin 128 := ![1, 27, 33, 34, 5]
def s35 : Fin 9 → Fin 128 := ![27, 1, 35, 36, 37, 38, 39, 40, 5]
def d42 : Fin 11 → Fin 128 := ![35, 41, 42, 43, 44, 45, 46, 47, 48, 49, 5]

def sys2M (r : Bool) :=
  Composition.machine (subM s35) (Composition.machine (wordM false (1 : Fin 128) 41 5)
  (Composition.machine (divmodM d42) (chainM ((sys2W r 0 0).map Wr.shape)).2))

def sys12M (r : Bool) :=
  Composition.machine (subM s27) (Composition.machine (testM t33)
    (CloseoutRowsOriginalSwitch.machine (sys2M r) (chainM ((sys1W r 0).map Wr.shape)).2 (33 : Fin 128)))

/-- **The systematic side's decode.** -/
def sysM (r : Bool) :=
  Composition.machine (constM [true] (24 : Fin 128) 5) (Composition.machine (testM t25)
    (CloseoutRowsOriginalSwitch.machine (sys12M r) (chainM ((sys0W r).map Wr.shape)).2 (25 : Fin 128)))

theorem sys_run (r : Bool) (x J Qx QJ Qf S C : Nat) (E : Fin 128 → List Bool)
    (hx : x < MonomialSpec.penLen true J) (hS : curBig J 0 ≤ S) (hC : curBig J 0 ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qx (List.replicate x true)) (h1 : E 1 = ZeroPadding.pad QJ (List.replicate J true))
    (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 128, 6 ≤ j.val → j.val < 80 → E j = List.replicate S false) :
    ∃ E' : Fin 128 → List Bool, Step (sysM r) (15 * curBig J 0) (fun _ => 0) E (fun _ => 0) E' ∧
      CursorOut (((penSide true r J)[x]?).map halfSel) S E' ∧
      (∀ j : Fin 128, j.val < 24 ∨ 80 ≤ j.val → j.val < 6 ∨ 24 ≤ j.val → E' j = E j) ∧ LenOK S E E' := by
  -- sizes
  set M := J + 0 + 2 with hM
  obtain ⟨p1, p2, p3, p4, p5⟩ := SourceFactorSel.Count.pow_facts J M (by omega) (by omega)
  have hbig : curBig J 0 = 64 * (M * M * (M * M)) := rfl
  have hxl : x < 1 + (J + J * J) := hx
  have hS1 : 1 ≤ S := by omega
  -- stage 1: `1^1` on 24
  set A1 := Function.update E 24 (ZeroPadding.pad S [true]) with hA1
  have s1 := const_step [true] (24 : Fin 128) 5 (by decide) S C (by simp; omega) (fun _ => 0) E rfl rfl
    (hscr 24 (by decide) (by decide)) h5
  -- stage 2: `[1 ≤ x]` on 25
  obtain ⟨A2, s2, a25, f2, l2⟩ := testI t25 (by decide) 25 27 (by decide) 1 x S Qx S C (by omega) (by omega) A1
    (by simp [t25, A1]) (by simp [t25, A1, h0]) (by simp [t25, A1, hscr 25 (by decide) (by decide)])
    (by simp [t25, A1, hscr 26 (by decide) (by decide)]) (by simp [t25, A1, h5])
  replace a25 : A2 25 = ZeroPadding.pad S [decide (1 ≤ x)] := a25
  have k2 : ∀ z : Fin 128, z.val < 24 ∨ 27 ≤ z.val → z.val ≠ 24 → A2 z = E z := by
    intro z hz h24
    rw [f2 z (by omega)]
    exact Function.update_of_ne (fun e => h24 (by rw [e]; rfl)) _ _
  have L2 : LenOK S E A2 := (LenOK.update E 24 [true] (by simp; omega)).trans l2
  by_cases hb : 1 ≤ x
  · -- `x ≥ 1`: subtract one
    obtain ⟨A3, s3, a27, f3, l3⟩ := subI s27 (by decide) 27 33 (by decide) x 1 Qx S S C hb (by omega) (by omega) A2
      (by simp [s27, k2 0 (by decide) (by decide), h0]) (by simp [s27, f2 24 (by decide), A1])
      (by
        intro j h2 h8
        have hv : 27 ≤ (s27 j).val ∧ (s27 j).val < 33 := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 →
          27 ≤ (s27 k).val ∧ (s27 k).val < 33 by decide) j h2 h8
        rw [k2 _ (by omega) (by omega)]; exact hscr _ (by omega) (by omega))
      (by simp [s27, k2 5 (by decide) (by decide), h5])
    replace a27 : A3 27 = ZeroPadding.pad S (List.replicate (x - 1) true) := a27
    have k3 : ∀ z : Fin 128, z.val < 24 ∨ 33 ≤ z.val → z.val ≠ 24 → z.val ≠ 25 → z.val ≠ 26 → A3 z = E z := by
      intro z hz h24 h25 h26
      rw [f3 z (by omega)]; exact k2 z (by omega) h24
    obtain ⟨A4, s4, a33, f4, l4⟩ := testI t33 (by decide) 33 35 (by decide) J (x - 1) QJ S S C (by omega) (by omega) A3
      (by simp [t33, k3 1 (by decide) (by decide) (by decide) (by decide), h1]) (by simp [t33, a27])
      (by simp [t33, k3 33 (by decide) (by decide) (by decide) (by decide), hscr 33 (by decide) (by decide)])
      (by simp [t33, k3 34 (by decide) (by decide) (by decide) (by decide), hscr 34 (by decide) (by decide)])
      (by simp [t33, k3 5 (by decide) (by decide) (by decide) (by decide), h5])
    replace a33 : A4 33 = ZeroPadding.pad S [decide (J ≤ x - 1)] := a33
    have L4 : LenOK S E A4 := L2.trans (l3.trans l4)
    have hA4_27 : A4 27 = ZeroPadding.pad S (List.replicate (x - 1) true) := (f4 27 (by decide)).trans a27
    have k4 : ∀ z : Fin 128, z.val < 24 ∨ 35 ≤ z.val → z.val ≠ 24 → z.val ≠ 25 → z.val ≠ 26 → A4 z = E z := by
      intro z hz h24 h25 h26
      rw [f4 z (by omega)]; exact k3 z (by omega) h24 h25 h26
    by_cases hb2 : J ≤ x - 1
    · -- block 2: `z = x - 1 - J`, two digits
      have hJ : 0 < J := by
        rcases Nat.eq_zero_or_pos J with h | h
        · subst h; simp at hxl; omega
        · exact h
      obtain ⟨A5, s5, a35, f5, l5⟩ := subI s35 (by decide) 35 41 (by decide) (x - 1) J S QJ S C hb2 (by omega)
        (by omega) A4 (by simp [s35, hA4_27]) (by simp [s35, k4 1 (by decide) (by decide) (by decide) (by decide), h1])
        (by
          intro j h2 h8
          have hv : 35 ≤ (s35 j).val ∧ (s35 j).val < 41 := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 →
            35 ≤ (s35 k).val ∧ (s35 k).val < 41 by decide) j h2 h8
          rw [k4 _ (by omega) (by omega) (by omega) (by omega)]; exact hscr _ (by omega) (by omega))
        (by simp [s35, k4 5 (by decide) (by decide) (by decide) (by decide), h5])
      replace a35 : A5 35 = ZeroPadding.pad S (List.replicate (x - 1 - J) true) := a35
      have k5 : ∀ z : Fin 128, z.val < 24 ∨ 41 ≤ z.val → z.val ≠ 24 → z.val ≠ 25 → z.val ≠ 26 → A5 z = E z := by
        intro z hz h24 h25 h26
        rw [f5 z (by omega)]; exact k4 z (by omega) h24 h25 h26
      set A6 := Function.update A5 41 (ZeroPadding.pad S (CompareMachine.word J)) with hA6
      have s6 := word0_step (1 : Fin 128) 41 5 (by decide) (by decide) (by decide) J QJ S C (by omega) (by omega)
        (fun _ => 0) A5 (fun _ _ => rfl) (by rw [k5 1 (by decide) (by decide) (by decide) (by decide)]; exact h1)
        (by rw [k5 41 (by decide) (by decide) (by decide) (by decide)]; exact hscr 41 (by decide) (by decide))
        (by rw [k5 5 (by decide) (by decide) (by decide) (by decide)]; exact h5)
      have hz2 : x - 1 - J < J * J := by omega
      obtain ⟨A7, s7, a42, a43, f7, l7⟩ := divI d42 (by decide) 42 50 (by decide) (x - 1 - J) J S S S C hJ
        (by omega) (by omega) (by omega) A6 (by simp [d42, A6, a35]) (by simp [d42, A6])
        (by
          intro j h2 h10
          have hv : 42 ≤ (d42 j).val ∧ (d42 j).val < 50 := (show ∀ k : Fin 11, 2 ≤ k.val → k.val < 10 →
            42 ≤ (d42 k).val ∧ (d42 k).val < 50 by decide) j h2 h10
          have hne : d42 j ≠ 41 := fun e => by rw [e] at hv; exact absurd hv.1 (by decide)
          rw [hA6, Function.update_of_ne hne, k5 _ (by omega) (by omega) (by omega) (by omega)]
          exact hscr _ (by omega) (by omega))
        (by simp [d42, A6, k5 5 (by decide) (by decide) (by decide) (by decide), h5])
      replace a42 : A7 42 = ZeroPadding.pad S (List.replicate ((x - 1 - J) / J) true) := a42
      replace a43 : A7 43 = ZeroPadding.pad S (List.replicate ((x - 1 - J) % J) true) := a43
      have L7 : LenOK S E A7 := L4.trans (l5.trans ((LenOK.update A5 41 _ (by simp [CompareMachine.word]; omega)).trans l7))
      have k7 : ∀ z : Fin 128, z.val < 24 ∨ 80 ≤ z.val → A7 z = E z := by
        intro z hz
        rw [f7 z (by omega), hA6, Function.update_of_ne (fun e => by rw [e] at hz; exact absurd hz (by decide))]
        exact k5 z (by omega) (by omega) (by omega) (by omega)
      have hq : (x - 1 - J) / J ≤ x := le_trans (Nat.div_le_self _ _) (by omega)
      have hu : (x - 1 - J) % J ≤ x := le_trans (Nat.mod_le _ _) (by omega)
      have s8 := chain_step S C (sys2W r ((x - 1 - J) / J) ((x - 1 - J) % J)) A7
        (by rw [k7 5 (by decide)]; exact h5)
        (by
          have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A7 z = List.replicate S false := fun z h6 h24 =>
            (k7 z (by omega)).trans (hscr z h6 (by omega))
          simp [sys2W, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, rec_len, a42, a43, b, ex_pad]
          omega)
      have e8 : (sys2W r ((x - 1 - J) / J) ((x - 1 - J) % J)).map Wr.shape = (sys2W r 0 0).map Wr.shape := rfl
      rw [e8] at s8
      have sw2 := CloseoutRowsOriginalSwitch.true_run (sys2M r) (chainM ((sys1W r 0).map Wr.shape)).2 (33 : Fin 128)
        (s5.seq (s6.seq (s7.seq s8))) (by show readTapeBit (A4 33) 0 = true; rw [a33, read_flag]; exact decide_eq_true hb2)
      have sw1 := CloseoutRowsOriginalSwitch.true_run (sys12M r) (chainM ((sys0W r).map Wr.shape)).2 (25 : Fin 128)
        (s3.seq (s4.seq sw2)) (by show readTapeBit (A2 25) 0 = true; rw [a25, read_flag]; exact decide_eq_true hb)
      have hall := s1.seq (s2.seq sw1)
      set E' := chainApp S (sys2W r ((x - 1 - J) / J) ((x - 1 - J) % J)) A7 with hE'
      have hσ := penSys_2 r J x (by omega) (by omega)
      refine ⟨E', hall.enlarge ?_, ?_, ?_, ?_⟩
      · rw [hbig]
        unfold testCost subCost divmodCost
        simp only [chainCost, sys2W, Wr.cost, rec_len, List.length_cons, List.length_nil]
        omega
      · have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A7 z = List.replicate S false := fun z h6 h24 =>
          (k7 z (by omega)).trans (hscr z h6 (by omega))
        rw [hσ]
        apply cursorOut_of <;>
          simp [hE', sys2W, chainApp, Wr.app, Wr.dst, Wr.out, facAt, fSys, fTerm, fSide, fIdx, kOf, rhoOf,
            halfSel, b, pad_ff S hS1, pad_zero, pad_nil', show x - (1 + J) = x - 1 - J by omega]
      · intro j hj1 hj2
        rw [hE', chainApp_other S _ A7 j (by
          intro w hw
          simp [sys2W] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [Wr.dst] <;> intro e <;> subst e <;> simp at hj1 hj2)]
        exact k7 j (by omega)
      · exact L7.trans (LenOK.chain _ A7 (by
          intro w hw
          simp [sys2W] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [Wr.out, ZeroPadding.pad_length, rec_len] <;> omega))
    · -- block 1: `[sys r, term r (x-1)]`
      have hy : x - 1 < J := by omega
      have k4' : ∀ z : Fin 128, z.val < 24 ∨ 80 ≤ z.val → A4 z = E z := fun z hz =>
        k4 z (by omega) (by omega) (by omega) (by omega)
      have s8 := chain_step S C (sys1W r (x - 1)) A4
        (by rw [k4' 5 (by decide)]; exact h5)
        (by
          have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A4 z = List.replicate S false := fun z h6 h24 =>
            (k4' z (by omega)).trans (hscr z h6 (by omega))
          simp [sys1W, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, rec_len, hA4_27, b, ex_pad]
          omega)
      have e8 : (sys1W r (x - 1)).map Wr.shape = (sys1W r 0).map Wr.shape := rfl
      rw [e8] at s8
      have sw2 := CloseoutRowsOriginalSwitch.false_run (sys2M r) (chainM ((sys1W r 0).map Wr.shape)).2 (33 : Fin 128)
        s8 (by show readTapeBit (A4 33) 0 = false; rw [a33, read_flag]; exact decide_eq_false hb2)
      have sw1 := CloseoutRowsOriginalSwitch.true_run (sys12M r) (chainM ((sys0W r).map Wr.shape)).2 (25 : Fin 128)
        (s3.seq (s4.seq sw2)) (by show readTapeBit (A2 25) 0 = true; rw [a25, read_flag]; exact decide_eq_true hb)
      have hall := s1.seq (s2.seq sw1)
      set E' := chainApp S (sys1W r (x - 1)) A4 with hE'
      have hσ := penSys_1 r J x hb hy
      refine ⟨E', hall.enlarge ?_, ?_, ?_, ?_⟩
      · rw [hbig]
        unfold testCost subCost
        simp only [chainCost, sys1W, Wr.cost, rec_len, List.length_cons, List.length_nil]
        omega
      · have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A4 z = List.replicate S false := fun z h6 h24 =>
          (k4' z (by omega)).trans (hscr z h6 (by omega))
        rw [hσ]
        apply cursorOut_of <;>
          simp [hE', sys1W, chainApp, Wr.app, Wr.dst, Wr.out, facAt, fSys, fTerm, fSide, fIdx, kOf, rhoOf,
            halfSel, b, pad_ff S hS1, pad_zero, pad_nil']
      · intro j hj1 hj2
        rw [hE', chainApp_other S _ A4 j (by
          intro w hw
          simp [sys1W] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [Wr.dst] <;> intro e <;> subst e <;> simp at hj1 hj2)]
        exact k4' j (by omega)
      · exact L4.trans (LenOK.chain _ A4 (by
          intro w hw
          simp [sys1W] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [Wr.out, ZeroPadding.pad_length, rec_len] <;> omega))
  · -- block 0: `x = 0`, `[sys r]`
    have hx0 : x = 0 := by omega
    subst hx0
    have k2' : ∀ z : Fin 128, z.val < 24 ∨ 80 ≤ z.val → A2 z = E z := fun z hz => k2 z (by omega) (by omega)
    have s8 := chain_step S C (sys0W r) A2 (by rw [k2' 5 (by decide)]; exact h5)
      (by
        have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A2 z = List.replicate S false := fun z h6 h24 =>
          (k2' z (by omega)).trans (hscr z h6 (by omega))
        simp [sys0W, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, rec_len, b]
        omega)
    have sw1 := CloseoutRowsOriginalSwitch.false_run (sys12M r) (chainM ((sys0W r).map Wr.shape)).2 (25 : Fin 128)
      s8 (by show readTapeBit (A2 25) 0 = false; rw [a25, read_flag]; exact decide_eq_false hb)
    have hall := s1.seq (s2.seq sw1)
    set E' := chainApp S (sys0W r) A2 with hE'
    refine ⟨E', hall.enlarge ?_, ?_, ?_, ?_⟩
    · rw [hbig]
      unfold testCost
      simp only [chainCost, sys0W, Wr.cost, rec_len, List.length_cons, List.length_nil]
      omega
    · have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A2 z = List.replicate S false := fun z h6 h24 =>
        (k2' z (by omega)).trans (hscr z h6 (by omega))
      rw [penSys_0 r J]
      apply cursorOut_of <;>
        simp [hE', sys0W, chainApp, Wr.app, Wr.dst, Wr.out, facAt, fSys, fTerm, fSide, fIdx, kOf, rhoOf,
          halfSel, b, pad_ff S hS1, pad_zero, pad_nil']
    · intro j hj1 hj2
      rw [hE', chainApp_other S _ A2 j (by
        intro w hw
        simp [sys0W] at hw
        rcases hw with rfl | rfl | rfl | rfl <;>
          simp [Wr.dst] <;> intro e <;> subst e <;> simp at hj1 hj2)]
      exact k2' j (by omega)
    · exact L2.trans (LenOK.chain _ A2 (by
        intro w hw
        simp [sys0W] at hw
        rcases hw with rfl | rfl | rfl | rfl <;>
          simp [Wr.out, ZeroPadding.pad_length, rec_len] <;> omega))

/-! ## The auxiliary side (`s = false`) -/

def aux0W (r : Bool) (q u : Nat) : List Wr :=
  [.cp 28 9 q, .cp 29 13 u, .c 7 [true], .c 8 [r], .c 11 [true], .c 12 [r], .c 22 [true, true],
    .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (1 / 2))]
def aux1W (r : Bool) (a b c : Nat) : List Wr :=
  [.cp 53 9 a, .cp 54 13 b, .cp 46 17 c, .c 7 [true], .c 8 [r], .c 11 [true], .c 12 [r], .c 15 [true], .c 16 [r],
    .c 22 [true, true, true], .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (-1))]
def aux2W (r : Bool) (a b c d : Nat) : List Wr :=
  [.cp 67 9 a, .cp 68 13 b, .cp 60 17 c, .cp 52 21 d, .c 7 [true], .c 8 [r], .c 11 [true], .c 12 [r],
    .c 15 [true], .c 16 [r], .c 19 [true], .c 20 [r], .c 22 [true, true, true, true],
    .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (1 / 2))]

def t26 : Fin 5 → Fin 128 := ![25, 0, 26, 27, 5]
def d28 : Fin 11 → Fin 128 := ![0, 24, 28, 29, 30, 31, 32, 33, 34, 35, 5]
def s36 : Fin 9 → Fin 128 := ![0, 25, 36, 37, 38, 39, 40, 41, 5]
def t43 : Fin 5 → Fin 128 := ![42, 36, 43, 44, 5]
def d45 : Fin 11 → Fin 128 := ![36, 24, 45, 46, 47, 48, 49, 50, 51, 52, 5]
def d53 : Fin 11 → Fin 128 := ![45, 24, 53, 54, 55, 56, 57, 58, 59, 60, 5]
def s45 : Fin 9 → Fin 128 := ![36, 42, 45, 46, 47, 48, 49, 50, 5]
def d51 : Fin 11 → Fin 128 := ![45, 24, 51, 52, 53, 54, 55, 56, 57, 58, 5]
def d59 : Fin 11 → Fin 128 := ![51, 24, 59, 60, 61, 62, 63, 64, 65, 66, 5]
def d67 : Fin 11 → Fin 128 := ![59, 24, 67, 68, 69, 70, 71, 72, 73, 74, 5]

def aux0M (r : Bool) := Composition.machine (divmodM d28) (chainM ((aux0W r 0 0).map Wr.shape)).2
def aux1M (r : Bool) := Composition.machine (divmodM d45) (Composition.machine (divmodM d53)
  (chainM ((aux1W r 0 0 0).map Wr.shape)).2)
def aux2M (r : Bool) := Composition.machine (subM s45) (Composition.machine (divmodM d51)
  (Composition.machine (divmodM d59) (Composition.machine (divmodM d67) (chainM ((aux2W r 0 0 0 0).map Wr.shape)).2)))
def aux12M (r : Bool) := Composition.machine (subM s36) (Composition.machine (mulM (25 : Fin 128) 24 42 5)
  (Composition.machine (testM t43) (CloseoutRowsOriginalSwitch.machine (aux2M r) (aux1M r) (43 : Fin 128))))

/-- **The auxiliary side's decode.** -/
def auxM (r : Bool) :=
  Composition.machine (wordM false (1 : Fin 128) 24 5) (Composition.machine (mulM (1 : Fin 128) 24 25 5)
  (Composition.machine (testM t26) (CloseoutRowsOriginalSwitch.machine (aux12M r) (aux0M r) (26 : Fin 128))))

theorem vals11 (sl : Fin 11 → Fin 128) (lo hi : Nat)
    (h : ∀ k : Fin 11, 2 ≤ k.val → k.val < 10 → lo ≤ (sl k).val ∧ (sl k).val < hi) :
    ∀ k : Fin 11, 2 ≤ k.val → k.val < 10 → lo ≤ (sl k).val ∧ (sl k).val < hi := h

/-- The size facts every auxiliary block uses (`M = J + 2`). -/
theorem auxSizes (J : Nat) :
    J ≤ (J + 0 + 2) * (J + 0 + 2) * ((J + 0 + 2) * (J + 0 + 2)) ∧
    J * J ≤ (J + 0 + 2) * (J + 0 + 2) * ((J + 0 + 2) * (J + 0 + 2)) ∧
    J * J * J ≤ (J + 0 + 2) * (J + 0 + 2) * ((J + 0 + 2) * (J + 0 + 2)) ∧
    J * J * (J * J) ≤ (J + 0 + 2) * (J + 0 + 2) * ((J + 0 + 2) * (J + 0 + 2)) ∧
    16 ≤ (J + 0 + 2) * (J + 0 + 2) * ((J + 0 + 2) * (J + 0 + 2)) ∧
    curBig J 0 = 64 * ((J + 0 + 2) * (J + 0 + 2) * ((J + 0 + 2) * (J + 0 + 2))) ∧
    J * (2 * J + 3) = 2 * (J * J) + 3 * J ∧ J * J * (2 * J + 3) = 2 * (J * J * J) + 3 * (J * J) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := SourceFactorSel.Count.pow_facts J (J + 0 + 2) (by omega) (by omega)
  exact ⟨p1, p2, p3, p4, p5, rfl, by ring, by ring⟩

/-- Block 0 of the auxiliary side: `x < J²`, two digits. -/
theorem aux0_leaf (r : Bool) (x J Qx S C : Nat) (E A : Fin 128 → List Bool)
    (hxj : x < J * J) (hS : curBig J 0 ≤ S) (hC : curBig J 0 ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qx (List.replicate x true)) (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 128, 6 ≤ j.val → j.val < 80 → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 28 ≤ z.val → A z = E z)
    (h24 : A 24 = ZeroPadding.pad S (CompareMachine.word J)) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step (aux0M r) (2 * curBig J 0) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (((penSide false r J)[x]?).map halfSel) S E' ∧
      (∀ j : Fin 128, j.val < 6 ∨ 80 ≤ j.val → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨p1, p2, p3, p4, p5, hbig, e1, e2⟩ := auxSizes J
  have hS1 : 1 ≤ S := by omega
  have hJ : 0 < J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp at hxj
    · exact h
  obtain ⟨A4, s4, a28, a29, f4, l4⟩ := divI d28 (by decide) 28 36 (by decide) x J Qx S S C hJ (by omega)
    (by omega) (by omega) A (by simp [d28, hk 0 (by decide), h0]) (by simp [d28, h24])
    (by
      intro j h2 h10
      have hv := vals11 d28 28 36 (by decide) j h2 h10
      rw [hk _ (by omega)]; exact hscr _ (by omega) (by omega))
    (by simp [d28, hk 5 (by decide), h5])
  replace a28 : A4 28 = ZeroPadding.pad S (List.replicate (x / J) true) := a28
  replace a29 : A4 29 = ZeroPadding.pad S (List.replicate (x % J) true) := a29
  have k4 : ∀ z : Fin 128, z.val < 24 ∨ 80 ≤ z.val → A4 z = E z := fun z hz =>
    (f4 z (by omega)).trans (hk z (by omega))
  have hq1 : x / J ≤ x := Nat.div_le_self _ _
  have hq2 : x % J ≤ x := Nat.mod_le _ _
  have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A4 z = List.replicate S false := fun z h6 h24 =>
    (k4 z (by omega)).trans (hscr z h6 (by omega))
  have s5 := chain_step S C (aux0W r (x / J) (x % J)) A4 (by rw [k4 5 (by decide)]; exact h5)
    (by
      simp [aux0W, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, rec_len, a28, a29, b, ex_pad]
      omega)
  have e5 : (aux0W r (x / J) (x % J)).map Wr.shape = (aux0W r 0 0).map Wr.shape := rfl
  rw [e5] at s5
  set E' := chainApp S (aux0W r (x / J) (x % J)) A4 with hE'
  refine ⟨E', (s4.seq s5).enlarge ?_, ?_, ?_, ?_⟩
  · rw [hbig]
    unfold divmodCost
    simp only [chainCost, aux0W, Wr.cost, rec_len, List.length_cons, List.length_nil]
    omega
  · rw [penAux_0 r J x hxj]
    apply cursorOut_of <;>
      simp [hE', aux0W, chainApp, Wr.app, Wr.dst, Wr.out, facAt, fSys, fTerm, fSide, fIdx, kOf, rhoOf,
        halfSel, b, pad_ff S hS1, pad_zero, pad_nil']
  · intro j hj
    rw [hE', chainApp_other S _ A4 j (by
      intro u hu
      simp [aux0W] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Wr.dst] <;> intro e <;> subst e <;> simp at hj)]
    exact k4 j (by omega)
  · exact (L.trans l4).trans (LenOK.chain _ A4 (by
      intro u hu
      simp [aux0W] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Wr.out, ZeroPadding.pad_length, rec_len] <;> omega))

/-- Block 1 of the auxiliary side: `z = x - J²`, `z < J³`, three digits. -/
theorem aux1_leaf (r : Bool) (x J S C : Nat) (E A : Fin 128 → List Bool)
    (hb : J * J ≤ x) (hzl : x - J * J < J * J * J) (hS : curBig J 0 ≤ S) (hC : curBig J 0 ≤ C)
    (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 128, 6 ≤ j.val → j.val < 80 → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 45 ≤ z.val → A z = E z)
    (h24 : A 24 = ZeroPadding.pad S (CompareMachine.word J))
    (h36 : A 36 = ZeroPadding.pad S (List.replicate (x - J * J) true)) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step (aux1M r) (2 * curBig J 0) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (((penSide false r J)[x]?).map halfSel) S E' ∧
      (∀ j : Fin 128, j.val < 6 ∨ 80 ≤ j.val → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨p1, p2, p3, p4, p5, hbig, e1, e2⟩ := auxSizes J
  have hS1 : 1 ≤ S := by omega
  have hJ : 0 < J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp at hzl
    · exact h
  set z := x - J * J with hz
  have hz1 : z / J ≤ z := Nat.div_le_self _ _
  obtain ⟨A7, s7, a45, a46, f7, l7⟩ := divI d45 (by decide) 45 53 (by decide) z J S S S C hJ (by omega)
    (by omega) (by omega) A (by simp [d45, h36]) (by simp [d45, h24])
    (by
      intro j h2 h10
      have hv := vals11 d45 45 53 (by decide) j h2 h10
      rw [hk _ (by omega)]; exact hscr _ (by omega) (by omega))
    (by simp [d45, hk 5 (by decide), h5])
  replace a45 : A7 45 = ZeroPadding.pad S (List.replicate (z / J) true) := a45
  replace a46 : A7 46 = ZeroPadding.pad S (List.replicate (z % J) true) := a46
  have hA7_24 : A7 24 = ZeroPadding.pad S (CompareMachine.word J) := (f7 24 (by decide)).trans h24
  have k7 : ∀ y : Fin 128, y.val < 24 ∨ 53 ≤ y.val → A7 y = E y := fun y hy =>
    (f7 y (by omega)).trans (hk y (by omega))
  obtain ⟨A8, s8, a53, a54, f8, l8⟩ := divI d53 (by decide) 53 61 (by decide) (z / J) J S S S C hJ (by omega)
    (by omega) (by omega) A7 (by simp [d53, a45]) (by simp [d53, hA7_24])
    (by
      intro j h2 h10
      have hv := vals11 d53 53 61 (by decide) j h2 h10
      rw [k7 _ (by omega)]; exact hscr _ (by omega) (by omega))
    (by simp [d53, k7 5 (by decide), h5])
  replace a53 : A8 53 = ZeroPadding.pad S (List.replicate (z / J / J) true) := a53
  replace a54 : A8 54 = ZeroPadding.pad S (List.replicate (z / J % J) true) := a54
  have hA8_46 : A8 46 = ZeroPadding.pad S (List.replicate (z % J) true) := (f8 46 (by decide)).trans a46
  have k8 : ∀ y : Fin 128, y.val < 24 ∨ 80 ≤ y.val → A8 y = E y := fun y hy =>
    (f8 y (by omega)).trans (k7 y (by omega))
  have hq1 : z / J / J ≤ z := le_trans (Nat.div_le_self _ _) hz1
  have hq2 : z / J % J ≤ z := le_trans (Nat.mod_le _ _) hz1
  have hq3 : z % J ≤ z := Nat.mod_le _ _
  have b : ∀ y : Fin 128, 6 ≤ y.val → y.val < 24 → A8 y = List.replicate S false := fun y h6 h24 =>
    (k8 y (by omega)).trans (hscr y h6 (by omega))
  have s9 := chain_step S C (aux1W r (z / J / J) (z / J % J) (z % J)) A8
    (by rw [k8 5 (by decide)]; exact h5)
    (by
      simp [aux1W, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, rec_len, a53, a54, hA8_46, b, ex_pad]
      omega)
  have e9 : (aux1W r (z / J / J) (z / J % J) (z % J)).map Wr.shape = (aux1W r 0 0 0).map Wr.shape := rfl
  rw [e9] at s9
  set E' := chainApp S (aux1W r (z / J / J) (z / J % J) (z % J)) A8 with hE'
  refine ⟨E', (s7.seq (s8.seq s9)).enlarge ?_, ?_, ?_, ?_⟩
  · rw [hbig]
    unfold divmodCost
    simp only [chainCost, aux1W, Wr.cost, rec_len, List.length_cons, List.length_nil]
    omega
  · rw [penAux_1 r J x hb hzl]
    apply cursorOut_of <;>
      simp [hE', aux1W, chainApp, Wr.app, Wr.dst, Wr.out, facAt, fSys, fTerm, fSide, fIdx, kOf, rhoOf,
        halfSel, b, pad_ff S hS1, pad_zero, pad_nil', hz]
  · intro j hj
    rw [hE', chainApp_other S _ A8 j (by
      intro u hu
      simp [aux1W] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Wr.dst] <;> intro e <;> subst e <;> simp at hj)]
    exact k8 j (by omega)
  · exact (L.trans (l7.trans l8)).trans (LenOK.chain _ A8 (by
      intro u hu
      simp [aux1W] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Wr.out, ZeroPadding.pad_length, rec_len] <;> omega))

/-- Block 2 of the auxiliary side: `w = x - J² - J³`, four digits. -/
theorem aux2_leaf (r : Bool) (x J S C : Nat) (E A : Fin 128 → List Bool)
    (hb : J * J ≤ x) (hb2 : J * J * J ≤ x - J * J) (hx : x < J * J + (J * J * J + J * J * (J * J)))
    (hS : curBig J 0 ≤ S) (hC : curBig J 0 ≤ C) (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 128, 6 ≤ j.val → j.val < 80 → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 45 ≤ z.val → A z = E z)
    (h24 : A 24 = ZeroPadding.pad S (CompareMachine.word J))
    (h36 : A 36 = ZeroPadding.pad S (List.replicate (x - J * J) true))
    (h42 : A 42 = ZeroPadding.pad S (List.replicate (J * J * J) true)) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step (aux2M r) (3 * curBig J 0) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (((penSide false r J)[x]?).map halfSel) S E' ∧
      (∀ j : Fin 128, j.val < 6 ∨ 80 ≤ j.val → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨p1, p2, p3, p4, p5, hbig, e1, e2⟩ := auxSizes J
  have hS1 : 1 ≤ S := by omega
  have hJ : 0 < J := by
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp at hx
    · exact h
  obtain ⟨A7, s7, a45, f7, l7⟩ := subI s45 (by decide) 45 51 (by decide) (x - J * J) (J * J * J) S S S C hb2
    (by omega) (by omega) A (by simp [s45, h36]) (by simp [s45, h42])
    (by
      intro j h2 h8
      have hv := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 → 45 ≤ (s45 k).val ∧ (s45 k).val < 51 by decide) j h2 h8
      rw [hk _ (by omega)]; exact hscr _ (by omega) (by omega))
    (by simp [s45, hk 5 (by decide), h5])
  set w := x - J * J - J * J * J with hw
  replace a45 : A7 45 = ZeroPadding.pad S (List.replicate w true) := a45
  have hA7_24 : A7 24 = ZeroPadding.pad S (CompareMachine.word J) := (f7 24 (by decide)).trans h24
  have k7 : ∀ z : Fin 128, z.val < 24 ∨ 51 ≤ z.val → A7 z = E z := fun z hz =>
    (f7 z (by omega)).trans (hk z (by omega))
  have hwl : w < J * J * (J * J) := by omega
  have hw1 : w / J ≤ w := Nat.div_le_self _ _
  have hw2 : w / J / J ≤ w := le_trans (Nat.div_le_self _ _) hw1
  obtain ⟨A8, s8, a51, a52, f8, l8⟩ := divI d51 (by decide) 51 59 (by decide) w J S S S C hJ (by omega)
    (by omega) (by omega) A7 (by simp [d51, a45]) (by simp [d51, hA7_24])
    (by
      intro j h2 h10
      have hv := vals11 d51 51 59 (by decide) j h2 h10
      rw [k7 _ (by omega)]; exact hscr _ (by omega) (by omega))
    (by simp [d51, k7 5 (by decide), h5])
  replace a51 : A8 51 = ZeroPadding.pad S (List.replicate (w / J) true) := a51
  replace a52 : A8 52 = ZeroPadding.pad S (List.replicate (w % J) true) := a52
  have hA8_24 : A8 24 = ZeroPadding.pad S (CompareMachine.word J) := (f8 24 (by decide)).trans hA7_24
  have k8 : ∀ z : Fin 128, z.val < 24 ∨ 59 ≤ z.val → A8 z = E z := fun z hz =>
    (f8 z (by omega)).trans (k7 z (by omega))
  obtain ⟨A9, s9, a59, a60, f9, l9⟩ := divI d59 (by decide) 59 67 (by decide) (w / J) J S S S C hJ (by omega)
    (by omega) (by omega) A8 (by simp [d59, a51]) (by simp [d59, hA8_24])
    (by
      intro j h2 h10
      have hv := vals11 d59 59 67 (by decide) j h2 h10
      rw [k8 _ (by omega)]; exact hscr _ (by omega) (by omega))
    (by simp [d59, k8 5 (by decide), h5])
  replace a59 : A9 59 = ZeroPadding.pad S (List.replicate (w / J / J) true) := a59
  replace a60 : A9 60 = ZeroPadding.pad S (List.replicate (w / J % J) true) := a60
  have hA9_24 : A9 24 = ZeroPadding.pad S (CompareMachine.word J) := (f9 24 (by decide)).trans hA8_24
  have hA9_52 : A9 52 = ZeroPadding.pad S (List.replicate (w % J) true) := (f9 52 (by decide)).trans a52
  have k9 : ∀ z : Fin 128, z.val < 24 ∨ 67 ≤ z.val → A9 z = E z := fun z hz =>
    (f9 z (by omega)).trans (k8 z (by omega))
  obtain ⟨A10, s10, a67, a68, f10, l10⟩ := divI d67 (by decide) 67 75 (by decide) (w / J / J) J S S S C hJ
    (by omega) (by omega) (by omega) A9 (by simp [d67, a59]) (by simp [d67, hA9_24])
    (by
      intro j h2 h10
      have hv := vals11 d67 67 75 (by decide) j h2 h10
      rw [k9 _ (by omega)]; exact hscr _ (by omega) (by omega))
    (by simp [d67, k9 5 (by decide), h5])
  replace a67 : A10 67 = ZeroPadding.pad S (List.replicate (w / J / J / J) true) := a67
  replace a68 : A10 68 = ZeroPadding.pad S (List.replicate (w / J / J % J) true) := a68
  have hA10_60 : A10 60 = ZeroPadding.pad S (List.replicate (w / J % J) true) := (f10 60 (by decide)).trans a60
  have hA10_52 : A10 52 = ZeroPadding.pad S (List.replicate (w % J) true) := (f10 52 (by decide)).trans hA9_52
  have k10 : ∀ z : Fin 128, z.val < 24 ∨ 80 ≤ z.val → A10 z = E z := fun z hz =>
    (f10 z (by omega)).trans (k9 z (by omega))
  have hq1 : w / J / J / J ≤ w := le_trans (Nat.div_le_self _ _) hw2
  have hq2 : w / J / J % J ≤ w := le_trans (Nat.mod_le _ _) hw2
  have hq3 : w / J % J ≤ w := le_trans (Nat.mod_le _ _) hw1
  have hq4 : w % J ≤ w := Nat.mod_le _ _
  have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A10 z = List.replicate S false := fun z h6 h24 =>
    (k10 z (by omega)).trans (hscr z h6 (by omega))
  have s11 := chain_step S C (aux2W r (w / J / J / J) (w / J / J % J) (w / J % J) (w % J)) A10
    (by rw [k10 5 (by decide)]; exact h5)
    (by
      simp [aux2W, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, rec_len, a67, a68, hA10_60, hA10_52, b, ex_pad]
      omega)
  have e11 : (aux2W r (w / J / J / J) (w / J / J % J) (w / J % J) (w % J)).map Wr.shape =
      (aux2W r 0 0 0 0).map Wr.shape := rfl
  rw [e11] at s11
  set E' := chainApp S (aux2W r (w / J / J / J) (w / J / J % J) (w / J % J) (w % J)) A10 with hE'
  have hσ := penAux_2 r J x (by omega) (by omega)
  have ew : x - (J * J + J * J * J) = w := by omega
  rw [ew] at hσ
  refine ⟨E', (s7.seq (s8.seq (s9.seq (s10.seq s11)))).enlarge ?_, ?_, ?_, ?_⟩
  · rw [hbig]
    unfold subCost divmodCost
    simp only [chainCost, aux2W, Wr.cost, rec_len, List.length_cons, List.length_nil]
    omega
  · rw [hσ]
    apply cursorOut_of <;>
      simp [hE', aux2W, chainApp, Wr.app, Wr.dst, Wr.out, facAt, fSys, fTerm, fSide, fIdx, kOf, rhoOf,
        halfSel, b, pad_ff S hS1, pad_zero, pad_nil']
  · intro j hj
    rw [hE', chainApp_other S _ A10 j (by
      intro u hu
      simp [aux2W] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Wr.dst] <;> intro e <;> subst e <;> simp at hj)]
    exact k10 j (by omega)
  · exact (L.trans (l7.trans (l8.trans (l9.trans l10)))).trans (LenOK.chain _ A10 (by
      intro u hu
      simp [aux2W] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Wr.out, ZeroPadding.pad_length, rec_len] <;> omega))

/-- Blocks 1–2 of the auxiliary side (`x ≥ J²`): `z = x - J²`, `1^(J³)`, the test `[J³ ≤ z]`, then the block. -/
theorem aux12_run (r : Bool) (x J Qx S C : Nat) (E A : Fin 128 → List Bool)
    (hb : J * J ≤ x) (hx : x < J * J + (J * J * J + J * J * (J * J))) (hS : curBig J 0 ≤ S) (hC : curBig J 0 ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qx (List.replicate x true)) (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 128, 6 ≤ j.val → j.val < 80 → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 28 ≤ z.val → A z = E z)
    (h24 : A 24 = ZeroPadding.pad S (CompareMachine.word J))
    (h25 : A 25 = ZeroPadding.pad S (List.replicate (J * J) true)) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step (aux12M r) (7 * curBig J 0) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (((penSide false r J)[x]?).map halfSel) S E' ∧
      (∀ j : Fin 128, j.val < 6 ∨ 80 ≤ j.val → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨p1, p2, p3, p4, p5, hbig, e1, e2⟩ := auxSizes J
  obtain ⟨A4, s4, a36, f4, l4⟩ := subI s36 (by decide) 36 42 (by decide) x (J * J) Qx S S C hb (by omega)
    (by omega) A (by simp [s36, hk 0 (by decide), h0]) (by simp [s36, h25])
    (by
      intro j h2 h8
      have hv := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 → 36 ≤ (s36 k).val ∧ (s36 k).val < 42 by decide) j h2 h8
      rw [hk _ (by omega)]; exact hscr _ (by omega) (by omega))
    (by simp [s36, hk 5 (by decide), h5])
  replace a36 : A4 36 = ZeroPadding.pad S (List.replicate (x - J * J) true) := a36
  have k4 : ∀ z : Fin 128, z.val < 24 ∨ 42 ≤ z.val → A4 z = E z := fun z hz =>
    (f4 z (by omega)).trans (hk z (by omega))
  have hA4_24 : A4 24 = ZeroPadding.pad S (CompareMachine.word J) := (f4 24 (by decide)).trans h24
  have hA4_25 : A4 25 = ZeroPadding.pad S (List.replicate (J * J) true) := (f4 25 (by decide)).trans h25
  set A5 := Function.update A4 42 (ZeroPadding.pad S (List.replicate (J * J * J) true)) with hA5
  have s5 := mul_step (25 : Fin 128) 24 42 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (J * J) J S S S C (by rw [e2]; omega) (fun _ => 0) A4 (fun _ _ => rfl) hA4_25 hA4_24
    (by rw [k4 42 (by decide)]; exact hscr 42 (by decide) (by decide)) (by rw [k4 5 (by decide)]; exact h5)
  obtain ⟨A6, s6, a43, f6, l6⟩ := testI t43 (by decide) 43 45 (by decide) (J * J * J) (x - J * J) S S S C
    (by omega) (by omega) A5 (by simp [t43, A5]) (by simp [t43, A5, a36])
    (by simp [t43, A5, k4 43 (by decide), hscr 43 (by decide) (by decide)])
    (by simp [t43, A5, k4 44 (by decide), hscr 44 (by decide) (by decide)])
    (by simp [t43, A5, k4 5 (by decide), h5])
  replace a43 : A6 43 = ZeroPadding.pad S [decide (J * J * J ≤ x - J * J)] := a43
  have hA6_24 : A6 24 = ZeroPadding.pad S (CompareMachine.word J) := by
    rw [f6 24 (by decide), hA5, Function.update_of_ne (by decide)]; exact hA4_24
  have hA6_36 : A6 36 = ZeroPadding.pad S (List.replicate (x - J * J) true) := by
    rw [f6 36 (by decide), hA5, Function.update_of_ne (by decide)]; exact a36
  have hA6_42 : A6 42 = ZeroPadding.pad S (List.replicate (J * J * J) true) := by
    rw [f6 42 (by decide)]; simp [A5]
  have k6 : ∀ z : Fin 128, z.val < 24 ∨ 45 ≤ z.val → A6 z = E z := by
    intro z hz
    have n42 : z ≠ 42 := fun e => by rw [e] at hz; exact absurd hz (by decide)
    rw [f6 z (by omega), hA5, Function.update_of_ne n42]; exact k4 z (by omega)
  have L6 : LenOK S E A6 := L.trans (l4.trans ((LenOK.update A4 42 _ (by simp; omega)).trans l6))
  by_cases hb2 : J * J * J ≤ x - J * J
  · obtain ⟨E', st, ho, hke, hl⟩ := aux2_leaf r x J S C E A6 hb hb2 hx hS hC h5 hscr k6 hA6_24 hA6_36 hA6_42 L6
    have sw := CloseoutRowsOriginalSwitch.true_run (aux2M r) (aux1M r) (43 : Fin 128) st
      (by show readTapeBit (A6 43) 0 = true; rw [a43, read_flag]; exact decide_eq_true hb2)
    refine ⟨E', (s4.seq (s5.seq (s6.seq sw))).enlarge ?_, ho, hke, hl⟩
    rw [hbig]; unfold subCost testCost; rw [e2]; omega
  · obtain ⟨E', st, ho, hke, hl⟩ := aux1_leaf r x J S C E A6 hb (by omega) hS hC h5 hscr k6 hA6_24 hA6_36 L6
    have sw := CloseoutRowsOriginalSwitch.false_run (aux2M r) (aux1M r) (43 : Fin 128) st
      (by show readTapeBit (A6 43) 0 = false; rw [a43, read_flag]; exact decide_eq_false hb2)
    refine ⟨E', (s4.seq (s5.seq (s6.seq sw))).enlarge ?_, ho, hke, hl⟩
    rw [hbig]; unfold subCost testCost; rw [e2]; omega

theorem aux_run (r : Bool) (x J Qx QJ Qf S C : Nat) (E : Fin 128 → List Bool)
    (hx : x < MonomialSpec.penLen false J) (hS : curBig J 0 ≤ S) (hC : curBig J 0 ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qx (List.replicate x true)) (h1 : E 1 = ZeroPadding.pad QJ (List.replicate J true))
    (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 128, 6 ≤ j.val → j.val < 80 → E j = List.replicate S false) :
    ∃ E' : Fin 128 → List Bool, Step (auxM r) (15 * curBig J 0) (fun _ => 0) E (fun _ => 0) E' ∧
      CursorOut (((penSide false r J)[x]?).map halfSel) S E' ∧
      (∀ j : Fin 128, j.val < 6 ∨ 80 ≤ j.val → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨p1, p2, p3, p4, p5, hbig, e1, e2⟩ := auxSizes J
  have hxl : x < J * J + (J * J * J + J * J * (J * J)) := hx
  set A1 := Function.update E 24 (ZeroPadding.pad S (CompareMachine.word J)) with hA1
  have s1 := word0_step (1 : Fin 128) 24 5 (by decide) (by decide) (by decide) J QJ S C (by omega) (by omega)
    (fun _ => 0) E (fun _ _ => rfl) h1 (hscr 24 (by decide) (by decide)) h5
  set A2 := Function.update A1 25 (ZeroPadding.pad S (List.replicate (J * J) true)) with hA2
  have s2 := mul_step (1 : Fin 128) 24 25 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    J J QJ S S C (by rw [e1]; omega) (fun _ => 0) A1 (fun _ _ => rfl) (by simp [A1, h1]) (by simp [A1])
    (by simp [A1, hscr 25 (by decide) (by decide)]) (by simp [A1, h5])
  obtain ⟨A3, s3, a26, f3, l3⟩ := testI t26 (by decide) 26 28 (by decide) (J * J) x S Qx S C (by omega) (by omega)
    A2 (by simp [t26, A2]) (by simp [t26, A1, A2, h0]) (by simp [t26, A1, A2, hscr 26 (by decide) (by decide)])
    (by simp [t26, A1, A2, hscr 27 (by decide) (by decide)]) (by simp [t26, A1, A2, h5])
  replace a26 : A3 26 = ZeroPadding.pad S [decide (J * J ≤ x)] := a26
  have hA3_24 : A3 24 = ZeroPadding.pad S (CompareMachine.word J) := by rw [f3 24 (by decide)]; simp [A1, A2]
  have hA3_25 : A3 25 = ZeroPadding.pad S (List.replicate (J * J) true) := by rw [f3 25 (by decide)]; simp [A2]
  have k3 : ∀ z : Fin 128, z.val < 24 ∨ 28 ≤ z.val → A3 z = E z := by
    intro z hz
    have n24 : z ≠ 24 := fun e => by rw [e] at hz; exact absurd hz (by decide)
    have n25 : z ≠ 25 := fun e => by rw [e] at hz; exact absurd hz (by decide)
    rw [f3 z (by omega), hA2, Function.update_of_ne n25, hA1, Function.update_of_ne n24]
  have L3 : LenOK S E A3 :=
    ((LenOK.update E 24 _ (by simp [CompareMachine.word]; omega)).trans
      (LenOK.update A1 25 _ (by simp; omega))).trans l3
  by_cases hb : J * J ≤ x
  · obtain ⟨E', st, ho, hke, hl⟩ := aux12_run r x J Qx S C E A3 hb hxl hS hC h0 h5 hscr k3 hA3_24 hA3_25 L3
    have sw := CloseoutRowsOriginalSwitch.true_run (aux12M r) (aux0M r) (26 : Fin 128) st
      (by show readTapeBit (A3 26) 0 = true; rw [a26, read_flag]; exact decide_eq_true hb)
    refine ⟨E', (s1.seq (s2.seq (s3.seq sw))).enlarge ?_, ho, hke, hl⟩
    rw [hbig]; unfold testCost; rw [e1]; omega
  · obtain ⟨E', st, ho, hke, hl⟩ := aux0_leaf r x J Qx S C E A3 (by omega) hS hC h0 h5 hscr k3 hA3_24 L3
    have sw := CloseoutRowsOriginalSwitch.false_run (aux12M r) (aux0M r) (26 : Fin 128) st
      (by show readTapeBit (A3 26) 0 = false; rw [a26, read_flag]; exact decide_eq_false hb)
    refine ⟨E', (s1.seq (s2.seq (s3.seq sw))).enlarge ?_, ho, hke, hl⟩
    rw [hbig]; unfold testCost; rw [e1]; omega

/-! ## One side: the aux flag selects the decode -/

/-- **Side `r`'s decode** (ONE fixed machine per side): aux flag `[!s]` on port `3`. -/
def sideM (r : Bool) := CloseoutRowsOriginalSwitch.machine (auxM r) (sysM r) (3 : Fin 128)

theorem side_run (r : Bool) : SideRun (sideM r) r := by
  intro s x J Qx QJ Qf S C E hx hS hC h0 h1 h3 h5 hscr
  cases s with
  | true =>
    obtain ⟨E', st, ho, hk, hl⟩ := sys_run r x J Qx QJ Qf S C E hx hS hC h0 h1 h5 hscr
    refine ⟨E', ?_, ho, fun j hj => hk j (by omega) (by omega), hl⟩
    have sw := CloseoutRowsOriginalSwitch.false_run (auxM r) (sysM r) (3 : Fin 128) st
      (by show readTapeBit (E 3) 0 = false; rw [h3, read_flag]; rfl)
    exact sw.enlarge (by have := curBig_ge J 0; omega)
  | false =>
    obtain ⟨E', st, ho, hk, hl⟩ := aux_run r x J Qx QJ Qf S C E hx hS hC h0 h1 h5 hscr
    refine ⟨E', ?_, ho, hk, hl⟩
    have sw := CloseoutRowsOriginalSwitch.true_run (auxM r) (sysM r) (3 : Fin 128) st
      (by show readTapeBit (E 3) 0 = true; rw [h3, read_flag]; rfl)
    exact sw.enlarge (by have := curBig_ge J 0; omega)

end
end NearCubicWires.SourceRequest.CurSide

