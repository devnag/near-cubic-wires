import Proof.SourceAssembly.SourceRequestCurSide

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CurPenalty
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp NearCubicWires.SourceRequest.CurWriter
open NearCubicWires.SourceRequest.CurSide
open NearCubicWires.SourceFactorSel.Count (read_flag)
noncomputable section

/-! ## Helpers -/

theorem sideCost_le (a : Bool) (J M : Nat) (hJ : J ≤ M) (hM : 2 ≤ M) :
    SourceFactorSel.Count.sideCost a J ≤ 60 * (M * M * (M * M)) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := SourceFactorSel.Count.pow_facts J M hJ hM
  have e1 : J * (2 * J + 3) = 2 * (J * J) + 3 * J := by ring
  have e2 : J * J * (2 * J + 3) = 2 * (J * J * J) + 3 * (J * J) := by ring
  have e3 : J * J * (2 * (J * J) + 3) = 2 * (J * J * (J * J)) + 3 * (J * J) := by ring
  cases a
  · simp only [SourceFactorSel.Count.sideCost, SourceFactorSel.Count.sysCost, Bool.false_eq_true, if_false, e1]
    omega
  · simp only [SourceFactorSel.Count.sideCost, SourceFactorSel.Count.auxCost, if_true, e1, e2, e3]
    omega

theorem curBig_mono (J JL JR : Nat) (h : J ≤ JL + JR) : curBig J 0 ≤ curBig JL JR := by
  unfold curBig
  have h1 : J + 0 + 2 ≤ JL + JR + 2 := by omega
  have h2 := Nat.mul_le_mul h1 h1
  exact Nat.mul_le_mul_left 64 (Nat.mul_le_mul h2 h2)

theorem gfSide (sl : Fin 10 → Fin 128) (hsl : Function.Injective sl) (lo hi : Nat)
    (hfp : ∀ j : Fin 10, 2 ≤ j.val → j.val < 9 → lo ≤ (sl j).val ∧ (sl j).val < hi)
    (aux : Bool) (J Q Qf S C : Nat) (A : Fin 128 → List Bool)
    (h0 : A (sl 0) = ZeroPadding.pad Q (List.replicate J true)) (h1 : A (sl 1) = ZeroPadding.pad Qf [aux])
    (hscr : ∀ j : Fin 10, 2 ≤ j.val → j.val < 9 → A (sl j) = List.replicate S false)
    (h9 : A (sl 9) = List.replicate C false) (hf : SourceFactorSel.Count.SideFits J S C)
    (hc : SourceFactorSel.Count.sideCost aux J + 1 ≤ S) :
    ∃ A' : Fin 128 → List Bool,
      Step (RecoveryFocus.machine sl SourceFactorSel.Count.side) (SourceFactorSel.Count.sideCost aux J)
        (fun _ => 0) A (fun _ => 0) A' ∧
      A' (sl 8) = ZeroPadding.pad S (List.replicate (MonomialSpec.penLen (!aux) J) true) ∧
      (∀ z : Fin 128, z.val < lo ∨ hi ≤ z.val → A' z = A z) ∧ LenOK S A A' := by
  obtain ⟨E', st, e8, e0, e1, e9⟩ :=
    SourceFactorSel.Count.side_run aux J Q Qf S C (fun i => A (sl i)) h0 h1 hscr h9 hf
  have keep : ∀ j : Fin 10, ¬ (2 ≤ j.val ∧ j.val < 9) → E' j = A (sl j) := by
    intro j hj
    have hv : j.val = 0 ∨ j.val = 1 ∨ j.val = 9 := by have := j.isLt; omega
    rcases hv with hv | hv | hv
    · rw [show j = 0 from Fin.ext hv]; exact e0
    · rw [show j = 1 from Fin.ext hv]; exact e1
    · rw [show j = 9 from Fin.ext hv]; exact e9
  refine ⟨install sl A E', TermSeg.dock st sl hsl _ A (fun _ => rfl) (fun _ => rfl), ?_, ?_, ?_⟩
  · rw [install_slot sl hsl]; exact e8
  · intro z hz
    by_cases hp : ∃ j, sl j = z
    · obtain ⟨j, rfl⟩ := hp
      rw [install_slot sl hsl]
      by_cases hj : 2 ≤ j.val ∧ j.val < 9
      · have := hfp j hj.1 hj.2; omega
      · exact keep j hj
    · exact install_other sl A E' z (fun j e => hp ⟨j, e⟩)
  · intro z
    by_cases hp : ∃ j, sl j = z
    · obtain ⟨j, rfl⟩ := hp
      rw [install_slot sl hsl]
      by_cases hj : 2 ≤ j.val ∧ j.val < 9
      · right
        exact P1Closure.LocalSupport.step_fits st j S (by show (A (sl j)).length ≤ S; rw [hscr j hj.1 hj.2]; simp)
          (by show 0 + SourceFactorSel.Count.sideCost aux J + 1 ≤ S; omega)
      · left; exact keep j hj
    · left; exact install_other sl A E' z (fun j e => hp ⟨j, e⟩)

/-- The right side's dock: `0 ↔ 96`, `1 ↔ 2`, `3 ↔ 4`. -/
def piR : Equiv.Perm (Fin 128) := Equiv.swap 0 96 * (Equiv.swap 1 2 * Equiv.swap 3 4)

theorem piR_mid : ∀ j : Fin 128, 5 ≤ j.val → j.val < 96 → piR j = j := by decide
theorem piR_out : ∀ j : Fin 128, j.val < 6 ∨ 80 ≤ j.val → (piR j).val < 6 ∨ 80 ≤ (piR j).val := by decide
theorem piR_invol : ∀ j : Fin 128, piR (piR j) = j := by decide

theorem cursorOut_congr {σ : Option Sel} {S : Nat} {E B : Fin 128 → List Bool} (h : CursorOut σ S E)
    (hB : ∀ p : Fin 128, 6 ≤ p.val → p.val < 24 → B p = E p) : CursorOut σ S B := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have := i.isLt
    rw [hB _ (by show 6 ≤ 6 + 4 * i.val; omega) (by show 6 + 4 * i.val < 24; omega)]; exact c1 i
  · have := i.isLt
    rw [hB _ (by show 6 ≤ 7 + 4 * i.val; omega) (by show 7 + 4 * i.val < 24; omega)]; exact c2 i
  · have := i.isLt
    rw [hB _ (by show 6 ≤ 8 + 4 * i.val; omega) (by show 8 + 4 * i.val < 24; omega)]; exact c3 i
  · have := i.isLt
    rw [hB _ (by show 6 ≤ 9 + 4 * i.val; omega) (by show 9 + 4 * i.val < 24; omega)]; exact c4 i
  · rw [hB _ (by decide) (by decide)]; exact c5
  · rw [hB _ (by decide) (by decide)]; exact c6

/-! ## The machine -/

def slPL : Fin 10 → Fin 128 := ![1, 3, 80, 81, 82, 83, 84, 85, 86, 5]
def slPR : Fin 10 → Fin 128 := ![2, 4, 89, 90, 91, 92, 93, 94, 95, 5]
def t87 : Fin 5 → Fin 128 := ![86, 0, 87, 88, 5]
def s96 : Fin 9 → Fin 128 := ![0, 86, 96, 97, 98, 99, 100, 101, 5]
def t102 : Fin 5 → Fin 128 := ![95, 96, 102, 103, 5]

def endM := constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5

def rightM :=
  Composition.machine (RecoveryFocus.machine slPR SourceFactorSel.Count.side)
  (Composition.machine (subM s96) (Composition.machine (testM t102)
    (CloseoutRowsOriginalSwitch.machine endM (RecoveryFocus.machine piR (sideM true)) (102 : Fin 128))))

/-- **The penalty cursor** (ONE fixed machine on the common layout). -/
def penaltyM :=
  Composition.machine (RecoveryFocus.machine slPL SourceFactorSel.Count.side)
  (Composition.machine (testM t87) (CloseoutRowsOriginalSwitch.machine rightM (sideM false) (87 : Fin 128)))

/-! ## Its run -/

/-- The right half (`m ≥ penLen sL JL`), from the bank after the left count and the first test. -/
theorem right_run (sL sR nL nR : Bool) (m JL JR Qm Q2 Qf S C : Nat) (E A : Fin 128 → List Bool)
    (hPL : MonomialSpec.penLen sL JL ≤ m) (hm : m ≤ MonomialSpec.penLen sL JL + MonomialSpec.penLen sR JR)
    (hS : curBig JL JR ≤ S) (hC : curBig JL JR ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qm (List.replicate m true)) (h2 : E 2 = ZeroPadding.pad Q2 (List.replicate JR true))
    (h4 : E 4 = ZeroPadding.pad Qf [!sR]) (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 128, 6 ≤ j.val → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 80 ∨ 89 ≤ z.val → A z = E z)
    (h86 : A 86 = ZeroPadding.pad S (List.replicate (MonomialSpec.penLen sL JL) true)) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool,
      Step rightM (40 * curBig JL JR) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (selAt .penalty sL sR nL nR JL JR m) S E' ∧
      (∀ j : Fin 128, j.val < 6 → E' j = E j) ∧ LenOK S E E' := by
  set M := JL + JR + 2 with hM
  obtain ⟨p1, p2, p3, p4, p5⟩ := SourceFactorSel.Count.pow_facts JR M (by omega) (by omega)
  have hbig : curBig JL JR = 64 * (M * M * (M * M)) := rfl
  have hPLb := SourceFactorSel.Count.penLen_le sL JL M (by omega) (by omega)
  have hPRb := SourceFactorSel.Count.penLen_le sR JR M (by omega) (by omega)
  have hsc := sideCost_le (!sR) JR M (by omega) (by omega)
  have hS1 : 1 ≤ S := by omega
  set PL := MonomialSpec.penLen sL JL with hPLd
  set PR := MonomialSpec.penLen sR JR with hPRd
  -- the right count `1^PR` on 95
  obtain ⟨A3, s3, a95, f3, l3⟩ := gfSide slPR (by decide) 89 96 (by decide) (!sR) JR Q2 Qf S C A
    (by simp [slPR, hk 2 (by decide), h2]) (by simp [slPR, hk 4 (by decide), h4])
    (by
      intro j h2' h9
      have hv := (show ∀ k : Fin 10, 2 ≤ k.val → k.val < 9 → 89 ≤ (slPR k).val ∧ (slPR k).val < 96 by decide) j h2' h9
      rw [hk _ (by omega)]; exact hscr _ (by omega))
    (by simp [slPR, hk 5 (by decide), h5])
    (SourceFactorSel.Count.sideFits_of JR M S C (by omega) (by omega) (by omega) (by omega)) (by omega)
  replace a95 : A3 95 = ZeroPadding.pad S (List.replicate PR true) := by
    have := a95; simp only [Bool.not_not] at this; exact this
  have k3 : ∀ z : Fin 128, z.val < 80 ∨ 96 ≤ z.val → z.val ≠ 86 → A3 z = E z := by
    intro z hz h86'
    rw [f3 z (by omega)]; exact hk z (by omega)
  have hA3_86 : A3 86 = ZeroPadding.pad S (List.replicate PL true) := (f3 86 (by decide)).trans h86
  -- `1^(m - PL)` on 96
  obtain ⟨A4, s4, a96, f4, l4⟩ := subI s96 (by decide) 96 102 (by decide) m PL Qm S S C hPL (by omega) (by omega)
    A3 (by simp [s96, k3 0 (by decide) (by decide), h0]) (by simp [s96, hA3_86])
    (by
      intro j h2' h8
      have hv := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 → 96 ≤ (s96 k).val ∧ (s96 k).val < 102 by decide) j h2' h8
      rw [k3 _ (by omega) (by omega)]; exact hscr _ (by omega))
    (by simp [s96, k3 5 (by decide) (by decide), h5])
  replace a96 : A4 96 = ZeroPadding.pad S (List.replicate (m - PL) true) := a96
  have hA4_95 : A4 95 = ZeroPadding.pad S (List.replicate PR true) := (f4 95 (by decide)).trans a95
  have k4 : ∀ z : Fin 128, z.val < 80 ∨ 102 ≤ z.val → z.val ≠ 86 → A4 z = E z := fun z hz h86' =>
    (f4 z (by omega)).trans (k3 z (by omega) h86')
  -- `[PR ≤ m - PL]` on 102
  obtain ⟨A5, s5, a102, f5, l5⟩ := testI t102 (by decide) 102 104 (by decide) PR (m - PL) S S S C (by omega)
    (by omega) A4 (by simp [t102, hA4_95]) (by simp [t102, a96])
    (by simp [t102, k4 102 (by decide) (by decide), hscr 102 (by decide)])
    (by simp [t102, k4 103 (by decide) (by decide), hscr 103 (by decide)])
    (by simp [t102, k4 5 (by decide) (by decide), h5])
  replace a102 : A5 102 = ZeroPadding.pad S [decide (PR ≤ m - PL)] := a102
  have hA5_96 : A5 96 = ZeroPadding.pad S (List.replicate (m - PL) true) := (f5 96 (by decide)).trans a96
  have k5 : ∀ z : Fin 128, z.val < 80 ∨ 104 ≤ z.val → z.val ≠ 86 → A5 z = E z := fun z hz h86' =>
    (f5 z (by omega)).trans (k4 z (by omega) h86')
  have L5 : LenOK S E A5 := L.trans (l3.trans (l4.trans l5))
  by_cases hb : PR ≤ m - PL
  · -- past the end
    have hmN : PL + PR ≤ m := by omega
    set E' := Function.update A5 23 (ZeroPadding.pad S (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0))
      with hE'
    have s6 := const_step (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5 (by decide) S C
      (by rw [rec_len]; omega) (fun _ => 0) A5 rfl rfl
      (by rw [k5 23 (by decide) (by decide)]; exact hscr 23 (by decide))
      (by rw [k5 5 (by decide) (by decide)]; exact h5)
    have sw := CloseoutRowsOriginalSwitch.true_run endM (RecoveryFocus.machine piR (sideM true)) (102 : Fin 128) s6
      (by show readTapeBit (A5 102) 0 = true; rw [a102, read_flag]; exact decide_eq_true hb)
    refine ⟨E', (s3.seq (s4.seq (s5.seq sw))).enlarge ?_, ?_, ?_, ?_⟩
    · rw [hbig]; unfold subCost testCost; rw [rec_len]; omega
    · rw [penalty_end sL sR nL nR JL JR m hmN]
      have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 23 → E' z = List.replicate S false := by
        intro z h6 h23
        have n23 : z ≠ 23 := fun e => by rw [e] at h23; exact absurd h23 (by decide)
        rw [hE', Function.update_of_ne n23, k5 z (by omega) (by omega)]; exact hscr z h6
      apply cursorOut_of <;> first
        | (rw [b _ (by decide) (by decide)]; simp [facAt, fSys, fTerm, fSide, fIdx, kOf, pad_ff S hS1, pad_nil'])
        | simp [hE', rhoOf]
    · intro j hj
      have n23 : j ≠ 23 := fun e => by rw [e] at hj; exact absurd hj (by decide)
      rw [hE', Function.update_of_ne n23]; exact k5 j (by omega) (by omega)
    · exact L5.trans (LenOK.update A5 23 _ (by rw [rec_len]; omega))
  · -- the right side's entry `m - PL`
    have hy : m - PL < PR := by omega
    obtain ⟨Eloc, st, ho, hke, hl⟩ := side_run true sR (m - PL) JR S Q2 Qf S C (fun i => A5 (piR i)) hy
      (le_trans (curBig_mono JR JL JR (by omega)) hS) (le_trans (curBig_mono JR JL JR (by omega)) hC)
      (by show A5 (piR 0) = _; rw [show piR 0 = 96 by decide]; exact hA5_96)
      (by show A5 (piR 1) = _; rw [show piR 1 = 2 by decide, k5 2 (by decide) (by decide)]; exact h2)
      (by show A5 (piR 3) = _; rw [show piR 3 = 4 by decide, k5 4 (by decide) (by decide)]; exact h4)
      (by show A5 (piR 5) = _; rw [show piR 5 = 5 by decide, k5 5 (by decide) (by decide)]; exact h5)
      (by
        intro j h6 h80
        show A5 (piR j) = _
        rw [piR_mid j (by omega) (by omega), k5 j (by omega) (by omega)]; exact hscr j h6)
    have dk := TermSeg.dock st piR piR.injective (fun _ => 0) A5 (fun _ => rfl) (fun _ => rfl)
    have sw := CloseoutRowsOriginalSwitch.false_run endM (RecoveryFocus.machine piR (sideM true)) (102 : Fin 128) dk
      (by show readTapeBit (A5 102) 0 = false; rw [a102, read_flag]; exact decide_eq_false hb)
    set E' := install piR A5 Eloc with hE'
    have hinst : ∀ z : Fin 128, E' z = Eloc (piR z) := by
      intro z
      have := install_slot piR piR.injective A5 Eloc (piR z)
      rw [piR_invol] at this
      exact this
    refine ⟨E', (s3.seq (s4.seq (s5.seq sw))).enlarge ?_, ?_, ?_, ?_⟩
    · have hmono := curBig_mono JR JL JR (by omega)
      rw [hbig] at hmono ⊢; unfold subCost testCost; omega
    · rw [penalty_right sL sR nL nR JL JR m hPL]
      refine cursorOut_congr ho ?_
      intro p h6 h24
      rw [hinst, piR_mid p (by omega) (by omega)]
    · intro j hj
      rw [hinst, hke (piR j) (piR_out j (Or.inl hj)), piR_invol]
      exact k5 j (by omega) (by omega)
    · refine L5.trans ?_
      intro z
      rw [hinst]
      rcases hl (piR z) with e | e
      · left; rw [e]; show A5 (piR (piR z)) = A5 z; rw [piR_invol]
      · right; exact e

/-- **The penalty cursor meets the common contract.** -/
theorem penalty_cursor : CursorRun penaltyM .penalty := by
  intro sL sR nL nR m JL JR Qm Q1 Q2 Qf S C E hm hS hC h0 h1 h2 h3 h4 h5 hscr
  replace h0 : E 0 = ZeroPadding.pad Qm (List.replicate m true) := h0
  replace h1 : E 1 = ZeroPadding.pad Q1 (List.replicate JL true) := h1
  replace h2 : E 2 = ZeroPadding.pad Q2 (List.replicate JR true) := h2
  replace h3 : E 3 = ZeroPadding.pad Qf [!sL] := h3
  replace h4 : E 4 = ZeroPadding.pad Qf [!sR] := h4
  replace h5 : E 5 = List.replicate C false := h5
  have hm' : m ≤ MonomialSpec.penLen sL JL + MonomialSpec.penLen sR JR := hm
  set M := JL + JR + 2 with hM
  obtain ⟨p1, p2, p3, p4, p5⟩ := SourceFactorSel.Count.pow_facts JL M (by omega) (by omega)
  have hbig : curBig JL JR = 64 * (M * M * (M * M)) := rfl
  have hPLb := SourceFactorSel.Count.penLen_le sL JL M (by omega) (by omega)
  have hsc := sideCost_le (!sL) JL M (by omega) (by omega)
  have hS1 : 1 ≤ S := by omega
  set PL := MonomialSpec.penLen sL JL with hPLd
  -- the left count `1^PL` on 86
  obtain ⟨A1, s1, a86, f1, l1⟩ := gfSide slPL (by decide) 80 87 (by decide) (!sL) JL Q1 Qf S C E
    (by simp [slPL, h1]) (by simp [slPL, h3])
    (by
      intro j h2' h9
      have hv := (show ∀ k : Fin 10, 2 ≤ k.val → k.val < 9 → 80 ≤ (slPL k).val ∧ (slPL k).val < 87 by decide) j h2' h9
      exact hscr _ (by omega))
    (by simp [slPL, h5])
    (SourceFactorSel.Count.sideFits_of JL M S C (by omega) (by omega) (by omega) (by omega)) (by omega)
  replace a86 : A1 86 = ZeroPadding.pad S (List.replicate PL true) := by
    have := a86; simp only [Bool.not_not] at this; exact this
  -- `[PL ≤ m]` on 87
  obtain ⟨A2, s2, a87, f2, l2⟩ := testI t87 (by decide) 87 89 (by decide) PL m S Qm S C (by omega) (by omega) A1
    (by simp [t87, a86]) (by simp [t87, f1 0 (by decide), h0])
    (by simp [t87, f1 87 (by decide), hscr 87 (by decide)]) (by simp [t87, f1 88 (by decide), hscr 88 (by decide)])
    (by simp [t87, f1 5 (by decide), h5])
  replace a87 : A2 87 = ZeroPadding.pad S [decide (PL ≤ m)] := a87
  have k2 : ∀ z : Fin 128, z.val < 80 ∨ 89 ≤ z.val → A2 z = E z := fun z hz =>
    (f2 z (by omega)).trans (f1 z (by omega))
  have hA2_86 : A2 86 = ZeroPadding.pad S (List.replicate PL true) := (f2 86 (by decide)).trans a86
  have L2 : LenOK S E A2 := l1.trans l2
  have fin : ∀ E' : Fin 128 → List Bool, LenOK S E E' → ∀ j : Fin 128, 24 ≤ j.val → (E' j).length ≤ S := by
    intro E' hl j hj
    rcases hl j with e | e
    · rw [e, hscr j (by omega)]; simp
    · exact e
  by_cases hb : PL ≤ m
  · obtain ⟨E', st, ho, hke, hl⟩ := right_run sL sR nL nR m JL JR Qm Q2 Qf S C E A2 hb hm' hS hC h0 h2 h4 h5 hscr
      k2 hA2_86 L2
    have sw := CloseoutRowsOriginalSwitch.true_run rightM (sideM false) (87 : Fin 128) st
      (by show readTapeBit (A2 87) 0 = true; rw [a87, read_flag]; exact decide_eq_true hb)
    refine ⟨E', (s1.seq (s2.seq sw)).enlarge ?_, ho, fun j hj => hke j hj, fin E' hl⟩
    unfold curCost; rw [hbig] at *; unfold testCost; omega
  · have hx : m < PL := Nat.lt_of_not_le hb
    obtain ⟨E', st, ho, hke, hl⟩ := side_run false sL m JL Qm Q1 Qf S C A2 hx
      (le_trans (curBig_mono JL JL JR (by omega)) hS) (le_trans (curBig_mono JL JL JR (by omega)) hC)
      (by rw [k2 0 (by decide)]; exact h0) (by rw [k2 1 (by decide)]; exact h1)
      (by rw [k2 3 (by decide)]; exact h3) (by rw [k2 5 (by decide)]; exact h5)
      (by intro j h6 h80; rw [k2 j (by omega)]; exact hscr j h6)
    have sw := CloseoutRowsOriginalSwitch.false_run rightM (sideM false) (87 : Fin 128) st
      (by show readTapeBit (A2 87) 0 = false; rw [a87, read_flag]; exact decide_eq_false hb)
    refine ⟨E', (s1.seq (s2.seq sw)).enlarge ?_, ?_, ?_, fin E' (L2.trans hl)⟩
    · have hmono := curBig_mono JL JL JR (by omega)
      unfold curCost; rw [hbig] at *; unfold testCost; omega
    · rw [penalty_left sL sR nL nR JL JR m hx]; exact ho
    · intro j hj
      rw [hke j (Or.inl hj)]; exact k2 j (by omega)

end
end NearCubicWires.SourceRequest.CurPenalty

