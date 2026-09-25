import Proof.SourceAssembly.SourceFactorSelDescF
import Proof.SourceAssembly.SourceRequestTermReaderRun
import Proof.SourceAssembly.SourceFactorSelCount

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Slot
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceFactorSel.Desc (Kind gdesc dT flagS flagO)
open NearCubicWires.SourceFactorSel.Count (read_flag wordM word0_step)
open NearCubicWires.SourceRequest.TermReader
noncomputable section

/-! ## The reader's dock -/

/-- The reader's tape `k` in the slot universe: its five inputs and coefficient output on the slot's ports, every other tape
(its code and count outputs included) at `40 + k`. -/
def rdS (k : Fin 1081) : Fin 1121 :=
  if k.val = 0 then 8 else if k.val = 188 then 34 else if k.val = 191 then 35
  else if k.val = 383 then 9 else if k.val = 538 then 10 else if k.val = 1079 then 33
  else ⟨40 + k.val, by omega⟩

theorem rdS_val (k : Fin 1081) : (rdS k).val =
    if k.val = 0 then 8 else if k.val = 188 then 34 else if k.val = 191 then 35
    else if k.val = 383 then 9 else if k.val = 538 then 10 else if k.val = 1079 then 33
    else 40 + k.val := by
  unfold rdS
  split_ifs <;> rfl

theorem rdS_inj : Function.Injective rdS := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have e := congrArg Fin.val h
  rw [rdS_val, rdS_val] at e
  apply Fin.ext
  split_ifs at e <;> omega

theorem rdS_code : rdS 535 = 575 := by decide
theorem rdS_out : rdS 1079 = 33 := by decide

/-- The reader's scratch sits at `≥ 40`. -/
theorem scr_ge (x : Fin 1121) (h : SourceRequest.TermReaderRun.scr rdS x) : 40 ≤ x.val := by
  obtain ⟨k, hk, rfl⟩ := h
  unfold SourceRequest.TermReaderRun.special at hk
  rw [rdS_val]
  split_ifs <;> omega

/-! ## The descriptor writer's docks -/

def descSl (b : Fin 1121) : Fin 27 → Fin 1121 :=
  ![0, 1, b, 575, 11, 12, 13, 14, 36, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

theorem descSl6_inj : Function.Injective (descSl 6) := by decide
theorem descSl7_inj : Function.Injective (descSl 7) := by decide

theorem descSl_dT (b : Fin 1121) (n : Fin 16) : descSl b (dT n) = ⟨17 + n.val, by omega⟩ := by
  fin_cases n <;> rfl

/-- The slot's descriptor port `n`. -/
def outP (n : Fin 16) : Fin 1121 := ⟨17 + n.val, by omega⟩

def descM (b : Fin 1121) := RecoveryFocus.machine (descSl b) DescF.machine

/-! ## The machine -/

def termM := Composition.machine
  (CloseoutRowsOriginalSwitch.machine (wordM false (5 : Fin 1121) 34 16) (wordM false (4 : Fin 1121) 34 16) (2 : Fin 1121))
  (Composition.machine (wordM false (3 : Fin 1121) 35 16)
  (Composition.machine (RecoveryFocus.machine rdS SourceRequest.TermCompose.machine) (descM 6)))

def otherM := CloseoutRowsOriginalSwitch.machine (descM 7) (descM 6) (2 : Fin 1121)

/-- **One factor slot's pipeline** (ONE fixed machine, both modes). -/
def slotM := CloseoutRowsOriginalSwitch.machine termM otherM (1 : Fin 1121)

theorem pad_false (Q : Nat) (h : 1 ≤ Q) : ZeroPadding.pad Q [false] = ZeroPadding.pad Q [] := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  simp [ZeroPadding.pad, List.replicate_succ]

/-- The slot's resident inputs (every one read-only). -/
structure Ins (A : Fin 1121 → List Bool) (tpl uP uW uL bmL bmR wbits : List Bool)
    (idx iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat) : Prop where
  i3 : A 3 = ZeroPadding.pad Qi (List.replicate idx true)
  i4 : A 4 = ZeroPadding.pad Qi (List.replicate iL true)
  i5 : A 5 = ZeroPadding.pad Qi (List.replicate iR true)
  i6 : A 6 = ZeroPadding.pad Qb bmL
  i7 : A 7 = ZeroPadding.pad Qb bmR
  i8 : A 8 = ZeroPadding.pad Rw (RepairOrdinary.frame wbits)
  i9 : A 9 = ZeroPadding.pad R (List.replicate cwid true)
  i10 : A 10 = ZeroPadding.pad R (List.replicate cw true)
  i11 : A 11 = ZeroPadding.pad Qt tpl
  i12 : A 12 = ZeroPadding.pad Qp uP
  i13 : A 13 = ZeroPadding.pad Qw uW
  i14 : A 14 = ZeroPadding.pad Ql uL
  i15 : A 15 = ZeroPadding.pad Qd (List.replicate D true)
  i16 : A 16 = List.replicate C false
  blank : ∀ j : Fin 1121, 17 ≤ j.val → A j = List.replicate R false

/-- The slot's width facts. -/
structure Fits (tpl uP uW uL : List Bool) (D R C : Nat) : Prop where
  tpl : tpl.length ≤ D
  uP : uP.length ≤ D
  uW : uW.length ≤ D
  uL : uL.length ≤ D
  d1 : 1 ≤ D
  dR : D ≤ R
  dC : D + 1 ≤ C

/-! ## The TERM branch -/

theorem term_run (k : Kind) (tpl uP uW uL bm cb bmL bmR wbits : List Bool) (r : Bool)
    (idx iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat) (ts : List (ℚ × Nat))
    (A : Fin 1121 → List Bool) (hk : k = .orig)
    (h0 : A 0 = ZeroPadding.pad Qf [false]) (h1 : A 1 = ZeroPadding.pad Qf [true]) (h2 : A 2 = ZeroPadding.pad Qf [r])
    (hQf : 1 ≤ Qf) (hin : Ins A tpl uP uW uL bmL bmR wbits idx iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hf : Fits tpl uP uW uL D R C)
    (hraw : rawTerms wbits (if r then iR else iL) = some ts) (hi : idx < ts.length)
    (hcb : cb = SignedSortKey.binary cwid ts[idx].2) (hcw : 2 * cwid + 1 ≤ D)
    (hcost : SourceRequest.TermCompose.readerCost wbits (if r then iR else iL) idx cwid cw + 1 ≤ R)
    (hjR : (if r then iR else iL) + 2 ≤ R) (hjC : (if r then iR else iL) + 3 ≤ C)
    (hiR : idx + 2 ≤ R) (hiC : idx + 3 ≤ C) :
    ∃ (H' : Fin 1121 → Nat) (A' : Fin 1121 → List Bool),
      Step termM ((2 * (if r then iR else iL) + 8 + 2) + 1 + ((2 * idx + 8) + 1 +
        (SourceRequest.TermCompose.readerCost wbits (if r then iR else iL) idx cwid cw + 1 + DescF.costF k D)))
        (fun _ => 0) A H' A' ∧
      (∀ n : Fin 16, A' (outP n) = ZeroPadding.pad R (gdesc tpl uP uW uL bm cb k n.val) ∧ H' (outP n) = 0) ∧
      A' 33 = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx].1) ∧ H' 33 = 0 ∧
      (∀ x : Fin 1121, x.val < 17 → A' x = A x ∧ H' x = 0) := by
  set jj := (if r then iR else iL) with hjj
  -- 1. `word j` on 34 (switch on the side flag)
  have sw : Step (CloseoutRowsOriginalSwitch.machine (wordM false (5 : Fin 1121) 34 16)
      (wordM false (4 : Fin 1121) 34 16) (2 : Fin 1121)) (2 * jj + 8 + 2) (fun _ => 0) A (fun _ => 0)
      (Function.update A 34 (ZeroPadding.pad R (CompareMachine.word jj))) := by
    cases r with
    | true =>
      exact CloseoutRowsOriginalSwitch.true_run _ _ (2 : Fin 1121)
        (word0_step (5 : Fin 1121) 34 16 (by decide) (by decide) (by decide) iR Qi R C hjR hjC (fun _ => 0) A
          (fun _ _ => rfl) hin.i5 (hin.blank 34 (by decide)) hin.i16)
        (by show readTapeBit (A 2) 0 = true; rw [h2, read_flag])
    | false =>
      exact CloseoutRowsOriginalSwitch.false_run _ _ (2 : Fin 1121)
        (word0_step (4 : Fin 1121) 34 16 (by decide) (by decide) (by decide) iL Qi R C hjR hjC (fun _ => 0) A
          (fun _ _ => rfl) hin.i4 (hin.blank 34 (by decide)) hin.i16)
        (by show readTapeBit (A 2) 0 = false; rw [h2, read_flag])
  set A1 := Function.update A 34 (ZeroPadding.pad R (CompareMachine.word jj)) with hA1
  -- 2. `word idx` on 35
  have w2 := word0_step (3 : Fin 1121) 35 16 (by decide) (by decide) (by decide) idx Qi R C hiR hiC (fun _ => 0) A1
    (fun _ _ => rfl) (by rw [hA1, Function.update_of_ne (by decide)]; exact hin.i3)
    (by rw [hA1, Function.update_of_ne (by decide)]; exact hin.blank 35 (by decide))
    (by rw [hA1, Function.update_of_ne (by decide)]; exact hin.i16)
  set A2 := Function.update A1 35 (ZeroPadding.pad R (CompareMachine.word idx)) with hA2
  have k2 : ∀ x : Fin 1121, x ≠ 34 → x ≠ 35 → A2 x = A x := by
    intro x a b
    rw [hA2, Function.update_of_ne b, hA1, Function.update_of_ne a]
  -- 3. the term reader
  have hR1 : 1 ≤ R := by omega
  obtain ⟨H3, A3, rd, o370, _, o535, h535, o1079, h1079, fr, _⟩ :=
    SourceRequest.TermReaderRun.readerRun rdS rdS_inj cwid cw wbits jj idx Rw R ts (fun _ => 0) A2 hraw hi
      (by rw [show rdS 0 = 8 by decide, k2 8 (by decide) (by decide)]; exact hin.i8) rfl
      (by rw [show rdS 188 = 34 by decide, hA2, Function.update_of_ne (by decide), hA1, Function.update_self]) rfl
      (by rw [show rdS 191 = 35 by decide, hA2, Function.update_self]) rfl
      (by rw [show rdS 383 = 9 by decide, k2 9 (by decide) (by decide)]; exact hin.i9) rfl
      (by rw [show rdS 538 = 10 by decide, k2 10 (by decide) (by decide)]; exact hin.i10) rfl
      (by
        intro x hx
        refine ⟨?_, rfl⟩
        have hx40 : 17 ≤ x.val ∧ x.val ≠ 34 ∧ x.val ≠ 35 := by
          rcases hx with h | h | h | h
          · have := scr_ge x h; omega
          · subst h; decide
          · subst h; decide
          · subst h; decide
        rw [k2 x (fun e => hx40.2.1 (by rw [e]; rfl)) (fun e => hx40.2.2 (by rw [e]; rfl))]
        exact hin.blank x hx40.1)
      hcost
  have k3 : ∀ x : Fin 1121, x.val < 40 → x.val ≠ 33 → A3 x = A2 x ∧ H3 x = 0 := by
    intro x h40 h33
    exact fr x (fun h => by have := scr_ge x h; omega)
      (fun e => by rw [e] at h40; exact absurd h40 (by decide))
      (fun e => by rw [e] at h40; exact absurd h40 (by decide))
      (fun e => h33 (by rw [e]; decide))
  rw [rdS_code] at o535 h535
  rw [rdS_out] at o1079 h1079
  -- 4. the descriptor writer on the reader's code
  have hA3 : ∀ x : Fin 1121, x.val < 34 → x.val ≠ 33 → A3 x = A x := fun x h h33 =>
    (k3 x (by omega) h33).1.trans (k2 x (fun e => by rw [e] at h; exact absurd h (by decide))
      (fun e => by rw [e] at h; exact absurd h (by decide)))
  obtain ⟨A4, ds, hE, hk4⟩ := DescF.slot_step (descSl 6) descSl6_inj k tpl uP uW uL bm cb Qf Qb R Qt Qp Qw Ql Qd D
    C R H3 A3
    (by
      intro j
      fin_cases j
      all_goals first
        | exact h535
        | exact (k3 _ (by decide) (by decide)).2)
    (by rw [show descSl 6 0 = 0 by rfl, hA3 0 (by decide) (by decide), h0, hk]; exact pad_false Qf hQf)
    (by rw [show descSl 6 1 = 1 by rfl, hA3 1 (by decide) (by decide), h1, hk]; rfl)
    (fun h => absurd (hk.symm.trans h) (by decide))
    (fun _ => ⟨by rw [show descSl 6 3 = 575 by rfl, o535, hcb],
      by rw [hcb]; simp [RepairOrdinary.frame, SignedSortKey.binary_length]; omega⟩)
    (by rw [show descSl 6 4 = 11 by rfl, hA3 11 (by decide) (by decide)]; exact hin.i11)
    (by rw [show descSl 6 5 = 12 by rfl, hA3 12 (by decide) (by decide)]; exact hin.i12)
    (by rw [show descSl 6 6 = 13 by rfl, hA3 13 (by decide) (by decide)]; exact hin.i13)
    (by rw [show descSl 6 7 = 14 by rfl, hA3 14 (by decide) (by decide)]; exact hin.i14)
    (by rw [show descSl 6 9 = 15 by rfl, hA3 15 (by decide) (by decide)]; exact hin.i15)
    (by rw [show descSl 6 10 = 16 by rfl, hA3 16 (by decide) (by decide)]; exact hin.i16)
    (by
      intro n
      rw [descSl_dT, hA3 _ (by simp; omega) (by simp; omega)]
      exact hin.blank _ (by simp))
    hf.tpl hf.uP hf.uW hf.uL hf.d1 hf.dR hf.dC
  refine ⟨H3, A4, sw.seq (w2.seq (rd.seq ds)), ?_, ?_, h1079, ?_⟩
  · intro n
    refine ⟨?_, (k3 (outP n) (by simp [outP]; omega) (by simp [outP]; omega)).2⟩
    have := hE n
    rw [descSl_dT] at this
    exact this
  · rw [hk4 33 (by intro n e; rw [descSl_dT] at e; have := congrArg Fin.val e; simp at this; omega)]
    exact o1079
  · intro x hx
    refine ⟨?_, (k3 x (by omega) (by omega)).2⟩
    rw [hk4 x (by intro n e; rw [descSl_dT] at e; rw [← e] at hx; simp at hx)]
    exact hA3 x (by omega) (by omega)

/-! ## The NOT-TERM branch (systematic or absent) -/

theorem other_run (k : Kind) (tpl uP uW uL bm cb bmL bmR wbits : List Bool) (s r : Bool)
    (idx iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat)
    (A : Fin 1121 → List Bool) (hk : k = if s then .sys else .absent)
    (h0 : A 0 = ZeroPadding.pad Qf [s]) (h1 : A 1 = ZeroPadding.pad Qf [false]) (h2 : A 2 = ZeroPadding.pad Qf [r])
    (hQf : 1 ≤ Qf) (hin : Ins A tpl uP uW uL bmL bmR wbits idx iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hf : Fits tpl uP uW uL D R C)
    (hbm : s = true → bm = (if r then bmR else bmL) ∧ bm.length ≤ D) :
    ∃ A' : Fin 1121 → List Bool,
      Step otherM (DescF.costF k D + 2) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ n : Fin 16, A' (outP n) = ZeroPadding.pad R (gdesc tpl uP uW uL bm cb k n.val)) ∧
      (∀ x : Fin 1121, x.val < 17 ∨ x.val = 33 → A' x = A x) := by
  have hfS : ZeroPadding.pad Qf [s] = ZeroPadding.pad Qf (flagS k) := by
    rw [hk]; cases s
    · exact pad_false Qf hQf
    · rfl
  have hfO : ZeroPadding.pad Qf [false] = ZeroPadding.pad Qf (flagO k) := by
    rw [hk]; cases s
    · exact pad_false Qf hQf
    · exact pad_false Qf hQf
  have common : ∀ (b : Fin 1121) (hb : Function.Injective (descSl b)), (b.val = 6 ∨ b.val = 7) →
      (k = .sys → A b = ZeroPadding.pad Qb bm ∧ bm.length ≤ D) →
      ∃ A' : Fin 1121 → List Bool, Step (descM b) (DescF.costF k D) (fun _ => 0) A (fun _ => 0) A' ∧
        (∀ n : Fin 16, A' (outP n) = ZeroPadding.pad R (gdesc tpl uP uW uL bm cb k n.val)) ∧
        (∀ x : Fin 1121, x.val < 17 ∨ x.val = 33 → A' x = A x) := by
    intro b hb hb67 hsys
    obtain ⟨A', ds, hE, hk4⟩ := DescF.slot_step (descSl b) hb k tpl uP uW uL bm cb Qf Qb R Qt Qp Qw Ql Qd D C R
      (fun _ => 0) A (fun _ => rfl) (by rw [show descSl b 0 = 0 by rfl, h0]; exact hfS)
      (by rw [show descSl b 1 = 1 by rfl, h1]; exact hfO) (fun h => hsys h)
      (fun h => by rw [hk] at h; cases s <;> simp at h)
      (by rw [show descSl b 4 = 11 by rfl]; exact hin.i11) (by rw [show descSl b 5 = 12 by rfl]; exact hin.i12)
      (by rw [show descSl b 6 = 13 by rfl]; exact hin.i13) (by rw [show descSl b 7 = 14 by rfl]; exact hin.i14)
      (by rw [show descSl b 9 = 15 by rfl]; exact hin.i15) (by rw [show descSl b 10 = 16 by rfl]; exact hin.i16)
      (by intro n; rw [descSl_dT]; exact hin.blank _ (by simp)) hf.tpl hf.uP hf.uW hf.uL hf.d1 hf.dR hf.dC
    refine ⟨A', ds, fun n => ?_, fun x hx => hk4 x ?_⟩
    · have := hE n; rw [descSl_dT] at this; exact this
    · intro n e; rw [descSl_dT] at e; rw [← e] at hx; simp at hx; omega
  cases r with
  | true =>
    obtain ⟨A', ds, hE, hk4⟩ := common 7 descSl7_inj (Or.inr rfl) (by
      intro h
      have hs : s = true := by rw [hk] at h; cases s <;> simp_all
      obtain ⟨e, hl⟩ := hbm hs
      exact ⟨by rw [hin.i7, e]; rfl, hl⟩)
    exact ⟨A', CloseoutRowsOriginalSwitch.true_run _ _ (2 : Fin 1121) ds
      (by show readTapeBit (A 2) 0 = true; rw [h2, read_flag]), hE, hk4⟩
  | false =>
    obtain ⟨A', ds, hE, hk4⟩ := common 6 descSl6_inj (Or.inl rfl) (by
      intro h
      have hs : s = true := by rw [hk] at h; cases s <;> simp_all
      obtain ⟨e, hl⟩ := hbm hs
      exact ⟨by rw [hin.i6, e]; rfl, hl⟩)
    exact ⟨A', CloseoutRowsOriginalSwitch.false_run _ _ (2 : Fin 1121) ds
      (by show readTapeBit (A 2) 0 = false; rw [h2, read_flag]), hE, hk4⟩

/-! ## The slot, mode-generic -/

/-- One cost bound for both branches (source polynomial). -/
def slotCost (wbits : List Bool) (jj idx cwid cw D : Nat) : Nat :=
  (2 * jj + 8 + 2) + 1 + ((2 * idx + 8) + 1 + (SourceRequest.TermCompose.readerCost wbits jj idx cwid cw + 1 +
    DescF.costF .orig D)) + 2 + (DescF.costF .sys D + DescF.costF .absent D + 4)

/-- What a TERM slot needs (the reader's inputs and windows). -/
def TermOK (wbits cb : List Bool) (jj idx cwid cw D R C : Nat) : Prop :=
  ∃ ts : List (ℚ × Nat), ∃ hi : idx < ts.length, rawTerms wbits jj = some ts ∧
    cb = SignedSortKey.binary cwid (ts[idx]'hi).2 ∧ 2 * cwid + 1 ≤ D ∧
    SourceRequest.TermCompose.readerCost wbits jj idx cwid cw + 1 ≤ R ∧
    jj + 2 ≤ R ∧ jj + 3 ≤ C ∧ idx + 2 ≤ R ∧ idx + 3 ≤ C

theorem termOK_of (wbits cb : List Bool) (jj idx cwid cw D R C : Nat) (ts : List (ℚ × Nat)) (hi : idx < ts.length)
    (hraw : rawTerms wbits jj = some ts) (hcb : cb = SignedSortKey.binary cwid (ts[idx]'hi).2)
    (hcw : 2 * cwid + 1 ≤ D) (hwin : SourceRequest.TermCompose.readerCost wbits jj idx cwid cw + 1 ≤ R)
    (hRC : R ≤ C) : TermOK wbits cb jj idx cwid cw D R C := by
  have a := Nat.le_mul_of_pos_right jj (show 0 < 2 * wbits.length + 4 by omega)
  have b := Nat.le_mul_of_pos_right idx
    (show 0 < 2 * (SourceRequest.TermCompose.cWord wbits jj).length + 4 by omega)
  have hw := hwin
  unfold SourceRequest.TermCompose.readerCost SourceRequest.TermSeg.costA SourceRequest.TermSegB.costB
    SourceRequest.TermSeg.seekCost CloseoutRowsTouching.FrameSeek.budget at hw
  exact ⟨ts, hi, hraw, hcb, hcw, hwin, by omega, by omega, by omega, by omega⟩

theorem gen_run (k : Kind) (tpl uP uW uL bm cb bmL bmR wbits : List Bool) (s t r : Bool)
    (idx iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat)
    (A : Fin 1121 → List Bool)
    (h0 : A 0 = ZeroPadding.pad Qf [s]) (h1 : A 1 = ZeroPadding.pad Qf [t]) (h2 : A 2 = ZeroPadding.pad Qf [r])
    (hQf : 1 ≤ Qf) (hin : Ins A tpl uP uW uL bmL bmR wbits idx iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hf : Fits tpl uP uW uL D R C)
    (hk : k = if s then .sys else if t then .orig else .absent) (hst : ¬ (s = true ∧ t = true))
    (hbm : s = true → bm = (if r then bmR else bmL) ∧ bm.length ≤ D)
    (hterm : t = true → TermOK wbits cb (if r then iR else iL) idx cwid cw D R C) :
    ∃ (H' : Fin 1121 → Nat) (A' : Fin 1121 → List Bool),
      Step slotM (slotCost wbits (if r then iR else iL) idx cwid cw D) (fun _ => 0) A H' A' ∧
      (∀ n : Fin 16, A' (outP n) = ZeroPadding.pad R (gdesc tpl uP uW uL bm cb k n.val) ∧ H' (outP n) = 0) ∧
      (t = true → ∀ ts, rawTerms wbits (if r then iR else iL) = some ts → ∀ hi : idx < ts.length,
        A' 33 = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx].1)) ∧
      H' 33 = 0 ∧
      (∀ x : Fin 1121, x.val < 17 → A' x = A x ∧ H' x = 0) := by
  cases t with
  | true =>
    have hs : s = false := by cases s <;> simp_all
    have hk' : k = .orig := by rw [hk, hs]; rfl
    obtain ⟨ts, hi, hraw, hcb, hcw, hcost, hjR, hjC, hiR, hiC⟩ := hterm rfl
    obtain ⟨H', A', st, hE, h33, hH33, hfr⟩ := term_run k tpl uP uW uL bm cb bmL bmR wbits r idx iL iR cwid cw D
      Qf Qi Qb Qt Qp Qw Ql Qd Rw R C ts A hk' (by rw [h0, hs]) h1 h2 hQf hin hf hraw hi hcb hcw hcost hjR hjC hiR hiC
    refine ⟨H', A', (CloseoutRowsOriginalSwitch.true_run termM otherM (1 : Fin 1121) st
      (by show readTapeBit (A 1) 0 = true; rw [h1, read_flag])).enlarge ?_, hE, ?_, hH33, hfr⟩
    · unfold slotCost; rw [hk']; omega
    · intro _ ts' hraw' hi'
      have e : ts' = ts := Option.some.inj (hraw'.symm.trans hraw)
      subst e
      exact h33
  | false =>
    have hk' : k = if s then .sys else .absent := by rw [hk]; cases s <;> rfl
    obtain ⟨A', st, hE, hfr⟩ := other_run k tpl uP uW uL bm cb bmL bmR wbits s r idx iL iR cwid cw D Qf Qi Qb Qt Qp
      Qw Ql Qd Rw R C A hk' h0 h1 h2 hQf hin hf hbm
    refine ⟨fun _ => 0, A', (CloseoutRowsOriginalSwitch.false_run termM otherM (1 : Fin 1121) st
      (by show readTapeBit (A 1) 0 = false; rw [h1, read_flag])).enlarge ?_, fun n => ⟨hE n, rfl⟩,
      fun h => absurd h (by decide), rfl, fun x hx => ⟨hfr x (Or.inl hx), rfl⟩⟩
    unfold slotCost; rw [hk']; cases s <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

/-! ## Per mode (the consumer's descriptors) -/

section
open RepairRepresentation SupplierPipeline SourceInterfaces SupplierEstimator NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceRequest
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf thr_descAt sym_descAt)

/-- **THR mode, one factor slot**: the slot's sixteen descriptors are `ThrSwitch.descAt P W L o n`, and a term slot's record is
its coefficient's `Product.record cw`. -/
theorem thr_slot_run (P W L : Nat) (o : Option (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp))
    (bmL bmR wbits : List Bool) (s t r : Bool) (idx iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat)
    (A : Fin 1121 → List Bool)
    (h0 : A 0 = ZeroPadding.pad Qf [s]) (h1 : A 1 = ZeroPadding.pad Qf [t]) (h2 : A 2 = ZeroPadding.pad Qf [r])
    (hQf : 1 ≤ Qf) (hin : Ins A (UnaryTemplate.tape q) (List.replicate P true) (List.replicate W true)
      (List.replicate L true) bmL bmR wbits idx iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hq : q + 2 ≤ D) (hP : P ≤ D) (hW : W ≤ D) (hL : L ≤ D) (hDR : D ≤ R) (hDC : D + 1 ≤ C)
    (hk : kindOf false o = if s then .sys else if t then .orig else .absent) (hst : ¬ (s = true ∧ t = true))
    (hbm : s = true → bmOf o = (if r then bmR else bmL) ∧ (bmOf o).length ≤ D)
    (hterm : t = true → TermOK wbits (bitsOf false L o) (if r then iR else iL) idx cwid cw D R C) :
    ∃ (H' : Fin 1121 → Nat) (A' : Fin 1121 → List Bool),
      Step slotM (slotCost wbits (if r then iR else iL) idx cwid cw D) (fun _ => 0) A H' A' ∧
      (∀ n : Fin 16, A' (outP n) = ZeroPadding.pad R (ThrSwitch.descAt P W L o n.val) ∧ H' (outP n) = 0) ∧
      (t = true → ∀ ts, rawTerms wbits (if r then iR else iL) = some ts → ∀ hi : idx < ts.length,
        A' 33 = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx].1)) ∧
      H' 33 = 0 ∧
      (∀ x : Fin 1121, x.val < 17 → A' x = A x ∧ H' x = 0) := by
  obtain ⟨H', A', st, hE, h33, hH33, hfr⟩ := gen_run (kindOf false o) (UnaryTemplate.tape q) (List.replicate P true)
    (List.replicate W true) (List.replicate L true) (bmOf o) (bitsOf false L o) bmL bmR wbits s t r idx iL iR cwid cw
    D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C A h0 h1 h2 hQf hin
    ⟨by rw [Modes.tape_length]; exact hq, by simpa using hP, by simpa using hW, by simpa using hL, by omega, hDR, hDC⟩
    hk hst hbm hterm
  exact ⟨H', A', st, fun n => ⟨by rw [thr_descAt]; exact (hE n).1, (hE n).2⟩, h33, hH33, hfr⟩

/-- **SYM mode, one factor slot.** -/
theorem sym_slot_run (P W L : Nat) (o : Option (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp))
    (bmL bmR wbits : List Bool) (s t r : Bool) (idx iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat)
    (A : Fin 1121 → List Bool)
    (h0 : A 0 = ZeroPadding.pad Qf [s]) (h1 : A 1 = ZeroPadding.pad Qf [t]) (h2 : A 2 = ZeroPadding.pad Qf [r])
    (hQf : 1 ≤ Qf) (hin : Ins A (UnaryTemplate.tape q) (List.replicate P true) (List.replicate W true)
      (List.replicate L true) bmL bmR wbits idx iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hq : q + 2 ≤ D) (hP : P ≤ D) (hW : W ≤ D) (hL : L ≤ D) (hDR : D ≤ R) (hDC : D + 1 ≤ C)
    (hk : kindOf true o = if s then .sys else if t then .orig else .absent) (hst : ¬ (s = true ∧ t = true))
    (hbm : s = true → bmOf o = (if r then bmR else bmL) ∧ (bmOf o).length ≤ D)
    (hterm : t = true → TermOK wbits (bitsOf true L o) (if r then iR else iL) idx cwid cw D R C) :
    ∃ (H' : Fin 1121 → Nat) (A' : Fin 1121 → List Bool),
      Step slotM (slotCost wbits (if r then iR else iL) idx cwid cw D) (fun _ => 0) A H' A' ∧
      (∀ n : Fin 16, A' (outP n) = ZeroPadding.pad R (SymSwitch.descAt P W L o n.val) ∧ H' (outP n) = 0) ∧
      (t = true → ∀ ts, rawTerms wbits (if r then iR else iL) = some ts → ∀ hi : idx < ts.length,
        A' 33 = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx].1)) ∧
      H' 33 = 0 ∧
      (∀ x : Fin 1121, x.val < 17 → A' x = A x ∧ H' x = 0) := by
  obtain ⟨H', A', st, hE, h33, hH33, hfr⟩ := gen_run (kindOf true o) (UnaryTemplate.tape q) (List.replicate P true)
    (List.replicate W true) (List.replicate L true) (bmOf o) (bitsOf true L o) bmL bmR wbits s t r idx iL iR cwid cw
    D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C A h0 h1 h2 hQf hin
    ⟨by rw [Modes.tape_length]; exact hq, by simpa using hP, by simpa using hW, by simpa using hL, by omega, hDR, hDC⟩
    hk hst hbm hterm
  exact ⟨H', A', st, fun n => ⟨by rw [sym_descAt]; exact (hE n).1, (hE n).2⟩, h33, hH33, hfr⟩

end

end
end NearCubicWires.SourceFactorSel.Slot

