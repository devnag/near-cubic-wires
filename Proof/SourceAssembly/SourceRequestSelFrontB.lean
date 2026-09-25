import Proof.SourceAssembly.SourceFactorSelCountRead
import Proof.SourceAssembly.SourceRequestCurMoment
import Proof.SourceAssembly.SourceRequestSelFrontA

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.SelFront
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
noncomputable section

/-! ## Docks -/

def crL (k : Fin 379) : Fin NF :=
  if k.val = 0 then 19 else if k.val = 188 then 200 else ⟨300 + k.val, by have := k.isLt; unfold NF; omega⟩
def crR (k : Fin 379) : Fin NF :=
  if k.val = 0 then 19 else if k.val = 188 then 201 else ⟨700 + k.val, by have := k.isLt; unfold NF; omega⟩

theorem crL_val (k : Fin 379) : (crL k).val = if k.val = 0 then 19 else if k.val = 188 then 200 else 300 + k.val := by
  unfold crL; split <;> [rfl; (split <;> rfl)]
theorem crR_val (k : Fin 379) : (crR k).val = if k.val = 0 then 19 else if k.val = 188 then 201 else 700 + k.val := by
  unfold crR; split <;> [rfl; (split <;> rfl)]

theorem crL_inj : Function.Injective crL := by
  intro x y h; have hv := congrArg Fin.val h; rw [crL_val, crL_val] at hv; apply Fin.ext
  split at hv <;> split at hv <;> (try split at hv) <;> (try split at hv) <;> omega
theorem crR_inj : Function.Injective crR := by
  intro x y h; have hv := congrArg Fin.val h; rw [crR_val, crR_val] at hv; apply Fin.ext
  split at hv <;> split at hv <;> (try split at hv) <;> (try split at hv) <;> omega

def fLp : Phase → Fin NF
  | .penalty => 185
  | .clause => 130
  | .moment => 250
def fRp : Phase → Fin NF
  | .penalty => 189
  | .clause => 142
  | .moment => 251

theorem fLp_val (ph : Phase) : (fLp ph).val = 185 ∨ (fLp ph).val = 130 ∨ (fLp ph).val = 250 := by
  cases ph <;> simp [fLp]
theorem fRp_val (ph : Phase) : (fRp ph).val = 189 ∨ (fRp ph).val = 142 ∨ (fRp ph).val = 251 := by
  cases ph <;> simp [fRp]

def ntSl (ph : Phase) (j : Fin 23) : Fin NF :=
  if j.val = 0 then 669 else if j.val = 1 then 1069 else if j.val = 2 then fLp ph else if j.val = 3 then fRp ph
  else if j.val = 4 then 33 else if j.val = 5 then 40 else ⟨1100 + j.val, by have := j.isLt; unfold NF; omega⟩

theorem ntSl_val (ph : Phase) (j : Fin 23) : (ntSl ph j).val =
    if j.val = 0 then 669 else if j.val = 1 then 1069 else if j.val = 2 then (fLp ph).val
    else if j.val = 3 then (fRp ph).val else if j.val = 4 then 33 else if j.val = 5 then 40 else 1100 + j.val := by
  unfold ntSl
  split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> rfl]]]]]

theorem ntSl_inj (ph : Phase) : Function.Injective (ntSl ph) := by
  intro x y h; have hv := congrArg Fin.val h; rw [ntSl_val, ntSl_val] at hv; apply Fin.ext
  have hL := fLp_val ph; have hR := fRp_val ph
  split at hv <;> split at hv <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
    (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
    (try split at hv) <;> (try split at hv) <;> omega

def curSl (ph : Phase) (j : Fin 128) : Fin NF :=
  if j.val = 0 then 20 else if j.val = 1 then 669 else if j.val = 2 then 1069 else if j.val = 3 then fLp ph
  else if j.val = 4 then fRp ph else if j.val = 5 then 41 else ⟨1200 + j.val, by have := j.isLt; unfold NF; omega⟩

theorem curSl_val (ph : Phase) (j : Fin 128) : (curSl ph j).val =
    if j.val = 0 then 20 else if j.val = 1 then 669 else if j.val = 2 then 1069 else if j.val = 3 then (fLp ph).val
    else if j.val = 4 then (fRp ph).val else if j.val = 5 then 41 else 1200 + j.val := by
  unfold curSl
  split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> rfl]]]]]

theorem curSl_inj (ph : Phase) : Function.Injective (curSl ph) := by
  intro x y h; have hv := congrArg Fin.val h; rw [curSl_val, curSl_val] at hv; apply Fin.ext
  have hL := fLp_val ph; have hR := fRp_val ph
  split at hv <;> split at hv <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
    (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
    (try split at hv) <;> (try split at hv) <;> omega

/-- The phase's cursor. -/
def curMach : Phase → (Σ s, Machine 128 s)
  | .moment => ⟨_, CurMoment.momentM⟩
  | .penalty => ⟨_, CurPenalty.penaltyM⟩
  | .clause => ⟨_, CurClause.clauseM⟩

theorem curRun (ph : Phase) : CursorRun (curMach ph).2 ph := by
  cases ph
  · exact CurPenalty.penalty_cursor
  · exact CurMoment.moment_cursor
  · exact CurClause.clause_cursor

/-- **Front B.** -/
def frontB (ph : Phase) :=
  Composition.machine (RecoveryFocus.machine crL SourceFactorSel.CountRead.countM)
  (Composition.machine (RecoveryFocus.machine crR SourceFactorSel.CountRead.countM)
  (Composition.machine (RecoveryFocus.machine (ntSl ph) (SourceFactorSel.Count.machine ph).2)
    (RecoveryFocus.machine (curSl ph) (curMach ph).2)))

theorem pen_flag (s i : Nat) (n : Bool) :
    decide (s ≤ i) = SourceFactorSel.Count.flagOf .penalty (decide (i < s)) n := by
  simp only [SourceFactorSel.Count.flagOf]
  by_cases h : i < s
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem crL0 : crL 0 = 19 := by unfold crL; rfl
theorem crL188 : crL 188 = 200 := by unfold crL; rfl
theorem crL369 : crL 369 = 669 := by unfold crL; rfl
theorem crR0 : crR 0 = 19 := by unfold crR; rfl
theorem crR188 : crR 188 = 201 := by unfold crR; rfl
theorem crR369 : crR 369 = 1069 := by unfold crR; rfl

theorem scrL_range (x : Fin NF) (h : SourceFactorSel.CountRead.scr crL x) : 300 ≤ x.val ∧ x.val < 679 := by
  obtain ⟨k, hk, rfl⟩ := h
  unfold SourceFactorSel.CountRead.special at hk
  rw [crL_val]; have := k.isLt
  split <;> [omega; (split <;> omega)]
theorem scrR_range (x : Fin NF) (h : SourceFactorSel.CountRead.scr crR x) : 700 ≤ x.val ∧ x.val < 1079 := by
  obtain ⟨k, hk, rfl⟩ := h
  unfold SourceFactorSel.CountRead.special at hk
  rw [crR_val]; have := k.isLt
  split <;> [omega; (split <;> omega)]

theorem big_le (JL JR : Nat) : SourceFactorSel.Count.big JL JR ≤ curBig JL JR := by
  unfold SourceFactorSel.Count.big curBig; omega

theorem ntSl4 (ph : Phase) : ntSl ph 4 = 33 := by unfold ntSl; rfl
theorem curSl0 (ph : Phase) : curSl ph 0 = 20 := by unfold curSl; rfl
theorem curSl1 (ph : Phase) : curSl ph 1 = 669 := by unfold curSl; rfl
theorem ntSl0 (ph : Phase) : ntSl ph 0 = 669 := by unfold ntSl; rfl
theorem ntSl1 (ph : Phase) : ntSl ph 1 = 1069 := by unfold ntSl; rfl
theorem ntSl2 (ph : Phase) : ntSl ph 2 = fLp ph := by unfold ntSl; rfl
theorem ntSl3 (ph : Phase) : ntSl ph 3 = fRp ph := by unfold ntSl; rfl
theorem curSl2 (ph : Phase) : curSl ph 2 = 1069 := by unfold curSl; rfl
theorem curSl3 (ph : Phase) : curSl ph 3 = fLp ph := by unfold curSl; rfl
theorem curSl4 (ph : Phase) : curSl ph 4 = fRp ph := by unfold curSl; rfl

def costB (ph : Phase) (bits : List Bool) (iL iR : Nat) (sL sR nL nR : Bool) (JL JR : Nat) : Nat :=
  SourceFactorSel.CountRead.countCost bits iL + 1 + (SourceFactorSel.CountRead.countCost bits iR + 1 +
    (SourceFactorSel.Count.cost ph sL sR nL nR JL JR + 1 + curCost JL JR))

/-- **Front B's run**: the two counts, `word N` on `nT`, and the phase cursor's record of monomial `m`. -/
theorem front_b (ph : Phase) (a : RepairRepresentation.PointwisePCPPAlgorithm)
    (r : RepairRepresentation.PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits)) (mode : Bool)
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (hread : CoordReads mode coordinate bits) (m Rc : Nat) (A : Fin NF → List Bool)
    (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length)
    (hcL : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length ≤ Rc)
    (hw : A 19 = RepairOrdinary.frame bits) (hcur : A 20 = ZeroPadding.pad Rc (List.replicate m true))
    (h185 : A 185 = ZeroPadding.pad Rc [decide ((a.output r).systematicBits ≤
      (literalIndex ((a.output r).clauses ci).left).val)])
    (h189 : A 189 = ZeroPadding.pad Rc [decide ((a.output r).systematicBits ≤
      (literalIndex ((a.output r).clauses ci).right).val)])
    (h130 : A 130 = ZeroPadding.pad Rc [literalNegated ((a.output r).clauses ci).left])
    (h142 : A 142 = ZeroPadding.pad Rc [literalNegated ((a.output r).clauses ci).right])
    (h200 : A 200 = ZeroPadding.pad Rc (CompareMachine.word (literalIndex ((a.output r).clauses ci).left).val))
    (h201 : A 201 = ZeroPadding.pad Rc (CompareMachine.word (literalIndex ((a.output r).clauses ci).right).val))
    (h33 : A 33 = List.replicate Rc false) (h40 : A 40 = List.replicate Rc false)
    (h41 : A 41 = List.replicate Rc false)
    (hblank : ∀ z : Fin NF, 202 ≤ z.val → A z = List.replicate Rc false) :
    ∃ (H' : Fin NF → Nat) (A' : Fin NF → List Bool),
      Step (frontB ph) (costB ph bits (literalIndex ((a.output r).clauses ci).left).val
        (literalIndex ((a.output r).clauses ci).right).val
        (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
        (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
        (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
        (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
        (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length) (fun _ => 0) A H' A' ∧
      A' 33 = ZeroPadding.pad Rc (CompareMachine.word (FactorLoop.monomials coordinate ph ci).length) ∧
      CursorOut (selAt ph (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
        (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
        (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
        (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
        (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length m) Rc
        (fun j => A' (curSl ph j)) ∧
      (∀ j : Fin 128, H' (curSl ph j) = 0) ∧ H' 33 = 0 ∧
      (∀ z : Fin NF, (z.val < 300 ∨ 1400 ≤ z.val) → z ≠ 33 → A' z = A z ∧ H' z = 0) := by
  set jL := literalIndex ((a.output r).clauses ci).left with hjL
  set jR := literalIndex ((a.output r).clauses ci).right with hjR
  set JL := (coordinate jL).monomials.length with hJL
  set JR := (coordinate jR).monomials.length with hJR
  set sL := decide (jL.val < (a.output r).systematicBits) with hsL
  set sR := decide (jR.val < (a.output r).systematicBits) with hsR
  set nL := literalNegated ((a.output r).clauses ci).left with hnL
  set nR := literalNegated ((a.output r).clauses ci).right with hnR
  obtain ⟨tsL, hrawL, hmapL, -⟩ := hread jL
  obtain ⟨tsR, hrawR, hmapR, -⟩ := hread jR
  have lenL : tsL.length = JL := by have := congrArg List.length hmapL; simp at this; omega
  have lenR : tsR.length = JR := by have := congrArg List.length hmapR; simp at this; omega
  have hbg := big_le JL JR
  have hRc1 : 1 ≤ Rc := by have := curBig_ge JL JR; omega
  -- count reader, left
  obtain ⟨H1, A1, s1, a669, h669, fr1, -⟩ := SourceFactorSel.CountRead.countRun crL crL_inj bits jL.val 0 Rc tsL
    (fun _ => 0) A hrawL (by rw [crL0, ZeroPadding.pad_zero]; exact hw) rfl (by rw [crL188]; exact h200) rfl
    (by
      intro x hx
      refine ⟨?_, rfl⟩
      rcases hx with hx | hx
      · exact hblank x (by have := scrL_range x hx; omega)
      · rw [hx, crL369]; exact hblank 669 (by decide)) hcL
  rw [crL369] at a669 h669
  have k1 : ∀ z : Fin NF, (z.val < 300 ∨ 679 ≤ z.val) → A1 z = A z ∧ H1 z = 0 := by
    intro z hz
    refine fr1 z (fun h => ?_) ?_
    · have := scrL_range z h; omega
    · rw [crL369]; intro e; rw [e] at hz; revert hz; decide
  -- count reader, right
  obtain ⟨H2, A2, s2, a1069, h1069, fr2, -⟩ := SourceFactorSel.CountRead.countRun crR crR_inj bits jR.val 0 Rc tsR
    H1 A1 hrawR (by rw [crR0, ZeroPadding.pad_zero, (k1 19 (by decide)).1]; exact hw) (by rw [crR0]; exact (k1 19 (by decide)).2)
    (by rw [crR188, (k1 201 (by decide)).1]; exact h201) (by rw [crR188]; exact (k1 201 (by decide)).2)
    (by
      intro x hx
      rcases hx with hx | hx
      · have := scrR_range x hx
        rw [(k1 x (by omega)).1, (k1 x (by omega)).2]; exact ⟨hblank x (by omega), rfl⟩
      · rw [hx, crR369, (k1 1069 (by decide)).1, (k1 1069 (by decide)).2]; exact ⟨hblank 1069 (by decide), rfl⟩) hcR
  rw [crR369] at a1069 h1069
  have k2 : ∀ z : Fin NF, (z.val < 300 ∨ 1079 ≤ z.val) → A2 z = A z ∧ H2 z = 0 := by
    intro z hz
    have e := fr2 z (fun h => by have := scrR_range z h; omega)
      (by rw [crR369]; intro e; rw [e] at hz; revert hz; decide)
    rw [e.1, e.2]; exact k1 z (by omega)
  have hA2_669 : A2 669 = ZeroPadding.pad Rc (List.replicate JL true) := by
    rw [(fr2 669 (fun h => by have := scrR_range 669 h; revert this; decide) (by rw [crR369]; decide)).1, a669, lenL]
  have hH2_669 : H2 669 = 0 := by
    rw [(fr2 669 (fun h => by have := scrR_range 669 h; revert this; decide) (by rw [crR369]; decide)).2, h669]
  have hA2_1069 : A2 1069 = ZeroPadding.pad Rc (List.replicate JR true) := by rw [a1069, lenR]
  have hH2 : ∀ z : Fin NF, (z.val < 300 ∨ 1079 ≤ z.val ∨ z.val = 669 ∨ z.val = 1069) → H2 z = 0 := by
    intro z hz
    rcases hz with hz | hz | hz | hz
    · exact (k2 z (Or.inl hz)).2
    · exact (k2 z (Or.inr hz)).2
    · rw [show z = 669 from Fin.ext hz]; exact hH2_669
    · rw [show z = 1069 from Fin.ext hz]; exact h1069
  -- the phase flags
  have fl : A2 (fLp ph) = ZeroPadding.pad Rc [SourceFactorSel.Count.flagOf ph sL nL] ∧
      A2 (fRp ph) = ZeroPadding.pad Rc [SourceFactorSel.Count.flagOf ph sR nR] ∧ H2 (fLp ph) = 0 ∧ H2 (fRp ph) = 0 := by
    cases ph
    · refine ⟨?_, ?_, (k2 185 (by decide)).2, (k2 189 (by decide)).2⟩
      · show A2 185 = _; rw [(k2 185 (by decide)).1, h185, pen_flag]
      · show A2 189 = _; rw [(k2 189 (by decide)).1, h189, pen_flag]
    · refine ⟨?_, ?_, (k2 250 (by decide)).2, (k2 251 (by decide)).2⟩
      · show A2 250 = _; rw [(k2 250 (by decide)).1, hblank 250 (by decide)]; exact (pad_ff Rc hRc1).symm
      · show A2 251 = _; rw [(k2 251 (by decide)).1, hblank 251 (by decide)]; exact (pad_ff Rc hRc1).symm
    · refine ⟨?_, ?_, (k2 130 (by decide)).2, (k2 142 (by decide)).2⟩
      · show A2 130 = _; rw [(k2 130 (by decide)).1, h130]; rfl
      · show A2 142 = _; rw [(k2 142 (by decide)).1, h142]; rfl
  obtain ⟨flL, flR, fhL, fhR⟩ := fl
  -- `word N`
  obtain ⟨A3, s3, a33, k3a, k3b, k3off⟩ := SourceFactorSel.Count.nT_step (ntSl ph) (ntSl_inj ph) coordinate ph ci Rc Rc
    Rc Rc Rc H2 A2
    (by
      intro j
      apply hH2
      have hL := fLp_val ph; have hR := fRp_val ph
      rw [ntSl_val]
      split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega)
    (by rw [ntSl0]; exact hA2_669) (by rw [ntSl1]; exact hA2_1069) (by rw [ntSl2]; exact flL) (by rw [ntSl3]; exact flR)
    (by rw [ntSl4, (k2 33 (by decide)).1]; exact h33)
    (by show A2 40 = _; rw [(k2 40 (by decide)).1]; exact h40)
    (by
      intro j hj
      have hv : (ntSl ph j).val = 1100 + j.val := by
        rw [ntSl_val]; simp [show j.val ≠ 0 by omega, show j.val ≠ 1 by omega, show j.val ≠ 2 by omega,
          show j.val ≠ 3 by omega, show j.val ≠ 4 by omega, show j.val ≠ 5 by omega]
      have := j.isLt
      rw [(k2 (ntSl ph j) (by omega)).1]
      exact hblank _ (by omega))
    (le_trans hbg hbig) (le_trans hbg hbig) (le_trans hbg hbig)
  rw [ntSl4] at a33
  have k3 : ∀ z : Fin NF, (z.val < 300 ∨ 1123 ≤ z.val) → z ≠ 33 → A3 z = A2 z := by
    intro z hz h33'
    by_cases hp : ∃ j, ntSl ph j = z
    · obtain ⟨j, rfl⟩ := hp
      by_cases hj : j.val < 4
      · exact k3a j hj
      · by_cases hj5 : j.val = 5
        · have : j = 5 := Fin.ext hj5
          subst this; exact k3b
        · by_cases hj4 : j.val = 4
          · have : j = 4 := Fin.ext hj4
            subst this; exact absurd (ntSl4 ph) h33'
          · exfalso; rw [ntSl_val] at hz; simp [show j.val ≠ 0 by omega, show j.val ≠ 1 by omega,
              show j.val ≠ 2 by omega, show j.val ≠ 3 by omega, hj4, hj5] at hz; have := j.isLt; omega
    · exact k3off z (fun j e => hp ⟨j, e⟩)
  -- the cursor
  have hm' : m ≤ MonomialSpec.siteLen ph sL sR nL nR JL JR := by
    rw [← MonomialSpec.monomials_len]; exact hm
  obtain ⟨E', s4, hout, hkeep, -⟩ := CursorRun.dock (curRun ph) (curSl ph) (curSl_inj ph) sL sR nL nR m JL JR Rc Rc Rc Rc
    Rc Rc H2 A3
    (by
      intro j
      apply hH2
      have hL := fLp_val ph; have hR := fRp_val ph
      rw [curSl_val]
      split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega)
    hm' hbig hbig
    (by show A3 (curSl ph 0) = _; rw [curSl0, k3 20 (by decide) (by decide), (k2 20 (by decide)).1]; exact hcur)
    (by show A3 (curSl ph 1) = _; rw [curSl1, ← ntSl0 ph, k3a 0 (by decide), ntSl0]; exact hA2_669)
    (by show A3 (curSl ph 2) = _; rw [curSl2, ← ntSl1 ph, k3a 1 (by decide), ntSl1]; exact hA2_1069)
    (by show A3 (curSl ph 3) = _; rw [curSl3, ← ntSl2 ph, k3a 2 (by decide), ntSl2]; exact flL)
    (by show A3 (curSl ph 4) = _; rw [curSl4, ← ntSl3 ph, k3a 3 (by decide), ntSl3]; exact flR)
    (by show A3 41 = _; rw [k3 41 (by decide) (by decide), (k2 41 (by decide)).1]; exact h41)
    (by
      intro j hj
      have hv : (curSl ph j).val = 1200 + j.val := by
        rw [curSl_val]; simp [show j.val ≠ 0 by omega, show j.val ≠ 1 by omega, show j.val ≠ 2 by omega,
          show j.val ≠ 3 by omega, show j.val ≠ 4 by omega, show j.val ≠ 5 by omega]
      have := j.isLt
      have n33 : curSl ph j ≠ 33 := fun e => by
        have h33v : (33 : Fin NF).val = 33 := rfl
        rw [e, h33v] at hv; omega
      rw [k3 (curSl ph j) (by omega) n33, (k2 (curSl ph j) (by omega)).1]
      exact hblank _ (by omega))
  refine ⟨H2, install (curSl ph) A3 E', s1.seq (s2.seq (s3.seq s4)), ?_, ?_, ?_, (k2 33 (by decide)).2, ?_⟩
  · rw [install_other (curSl ph) A3 E' 33 (fun j e => by
      have hv := congrArg Fin.val e; rw [curSl_val] at hv
      have h33v : (33 : Fin NF).val = 33 := rfl
      rw [h33v] at hv
      have hL := fLp_val ph; have hR := fRp_val ph
      split at hv <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
        (try split at hv) <;> omega)]
    exact a33
  · have e : (fun j => install (curSl ph) A3 E' (curSl ph j)) = E' := by
      funext j; exact install_slot (curSl ph) (curSl_inj ph) A3 E' j
    rw [e]; exact hout
  · intro j
    apply hH2
    have hL := fLp_val ph; have hR := fRp_val ph
    rw [curSl_val]
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
  · intro z hz h33'
    refine ⟨?_, (k2 z (by omega)).2⟩
    by_cases hp : ∃ j, curSl ph j = z
    · obtain ⟨j, rfl⟩ := hp
      rw [install_slot (curSl ph) (curSl_inj ph)]
      by_cases hj : j.val < 6
      · rw [hkeep j hj]
        rw [k3 _ (by omega) h33', (k2 _ (by omega)).1]
      · exfalso; rw [curSl_val] at hz
        simp [show j.val ≠ 0 by omega, show j.val ≠ 1 by omega, show j.val ≠ 2 by omega,
          show j.val ≠ 3 by omega, show j.val ≠ 4 by omega, show j.val ≠ 5 by omega] at hz
        have := j.isLt; omega
    · rw [install_other (curSl ph) A3 E' z (fun j e => hp ⟨j, e⟩), k3 z (by omega) h33', (k2 z (by omega)).1]

end
end NearCubicWires.SourceRequest.SelFront

