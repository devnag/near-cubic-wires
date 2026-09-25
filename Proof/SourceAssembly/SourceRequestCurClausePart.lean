import Proof.SourceAssembly.SourceRequestCurPenalty

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CurClause
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp NearCubicWires.SourceRequest.CurWriter
open NearCubicWires.SourceRequest.CurSide
open NearCubicWires.SourceFactorSel.Count (read_flag)
noncomputable section

/-! ## Spec -/

def pOf (n : Bool) (i : Nat) : Bool := !(n && decide (i = 0))
def iOf (n : Bool) (i : Nat) : Nat := i - n.toNat
def sOf (n : Bool) (i : Nat) : Bool := n && !decide (i = 0)

/-- The multiplier of a clause record. -/
def g (c a b : Bool) : ℚ := (if c then -1 else 1) * ((if a then -1 else 1) * (if b then -1 else 1))

/-- A clause monomial: left part, right part, multiplier. -/
def clauseRec (c pL pR : Bool) (iL iR : Nat) (sL sR : Bool) : Sel :=
  ⟨(if pL then [Fac.term false iL] else []) ++ (if pR then [Fac.term true iR] else []), g c sL sR⟩

theorem lit_as_rec_L (n : Bool) (i : Nat) :
    litEntry n false i = clauseRec false (pOf n i) false (iOf n i) 0 (sOf n i) false := by
  unfold litEntry clauseRec pOf iOf sOf g
  cases n <;> by_cases h : i = 0 <;> simp [h]

theorem lit_as_rec_R (n : Bool) (i : Nat) :
    litEntry n true i = clauseRec false false (pOf n i) 0 (iOf n i) false (sOf n i) := by
  unfold litEntry clauseRec pOf iOf sOf g
  cases n <;> by_cases h : i = 0 <;> simp [h]

theorem cross_as_rec (nL nR : Bool) (iL iR : Nat) :
    crossEntry nL nR iL iR =
      clauseRec true (pOf nL iL) (pOf nR iR) (iOf nL iL) (iOf nR iR) (sOf nL iL) (sOf nR iR) := by
  unfold crossEntry litEntry clauseRec pOf iOf sOf g
  cases nL <;> cases nR <;> by_cases hL : iL = 0 <;> by_cases hR : iR = 0 <;> simp [hL, hR]

/-! ## One literal's part decode (local `Fin 14`) -/

def posL := Composition.machine (constM [true] (2 : Fin 14) 13) (copyM (0 : Fin 14) 3 13)
def neg1L := Composition.machine (subM (![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14))
  (Composition.machine (constM [true] (2 : Fin 14) 13) (constM [true] (4 : Fin 14) 13))
def negL := Composition.machine (constM [true] (5 : Fin 14) 13)
  (Composition.machine (testM (![5, 0, 6, 7, 13] : Fin 5 → Fin 14))
    (CloseoutRowsOriginalSwitch.machine neg1L (CloseoutRowsOriginalSwitch.stop 14) (6 : Fin 14)))
/-- **One literal's part decode.** -/
def partL := CloseoutRowsOriginalSwitch.machine negL posL (1 : Fin 14)

def partCost (i : Nat) : Nat := 16 * i + 100

theorem part_run (n : Bool) (i Qi Qn S C : Nat) (E : Fin 14 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Qi (List.replicate i true)) (h1 : E 1 = ZeroPadding.pad Qn [n])
    (hscr : ∀ j : Fin 14, 2 ≤ j.val → j.val < 13 → E j = List.replicate S false)
    (h13 : E 13 = List.replicate C false) (hS : partCost i + 1 ≤ S) (hC : partCost i ≤ C) :
    ∃ E' : Fin 14 → List Bool, Step partL (partCost i) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 2 = ZeroPadding.pad S [pOf n i] ∧ E' 3 = ZeroPadding.pad S (List.replicate (iOf n i) true) ∧
      E' 4 = ZeroPadding.pad S [sOf n i] ∧ E' 0 = E 0 ∧ E' 1 = E 1 ∧ E' 13 = E 13 := by
  unfold partCost at hS hC
  have hS1 : 1 ≤ S := by omega
  cases n with
  | false =>
    set E1 := Function.update E 2 (ZeroPadding.pad S [true]) with hE1
    have s1 := const_step [true] (2 : Fin 14) 13 (by decide) S C (by simp; omega) (fun _ => 0) E rfl rfl
      (hscr 2 (by decide) (by decide)) h13
    have s2 := copy_step (0 : Fin 14) 3 13 (by decide) (by decide) (by decide) i Qi S C (by omega) (fun _ => 0) E1
      (fun _ _ => rfl) (by simp [E1, h0]) (by simp [E1, hscr 3 (by decide) (by decide)]) (by simp [E1, h13])
    have sw := CloseoutRowsOriginalSwitch.false_run negL posL (1 : Fin 14) (s1.seq s2)
      (by show readTapeBit (E 1) 0 = false; rw [h1, read_flag])
    refine ⟨_, sw.enlarge (by unfold partCost; simp; omega), by simp [E1, pOf], by simp [E1, iOf], ?_, by simp [E1], by simp [E1],
      by simp [E1]⟩
    simp [E1, sOf, hscr 4 (by decide) (by decide), pad_ff S hS1]
  | true =>
    set E1 := Function.update E 5 (ZeroPadding.pad S [true]) with hE1
    have s1 := const_step [true] (5 : Fin 14) 13 (by decide) S C (by simp; omega) (fun _ => 0) E rfl rfl
      (hscr 5 (by decide) (by decide)) h13
    obtain ⟨A2, s2, a6, f2, l7⟩ := test_step (![5, 0, 6, 7, 13] : Fin 5 → Fin 14) (by decide) 1 i S Qi S C
      (by omega) (by omega) (fun _ => 0) E1 (fun _ => rfl) (by simp [E1]) (by simp [E1, h0])
      (by simp [E1, hscr 6 (by decide) (by decide)]) (by simp [E1, hscr 7 (by decide) (by decide)])
      (by simp [E1, h13])
    replace a6 : A2 6 = ZeroPadding.pad S [decide (1 ≤ i)] := a6
    have f2' : ∀ z : Fin 14, z ≠ 6 → z ≠ 7 → A2 z = E1 z := fun z h6 h7 =>
      f2 z (fun e => h6 e.symm) (fun e => h7 e.symm)
    by_cases hi : 1 ≤ i
    · obtain ⟨A3, s3, a3, f3, l3⟩ := sub_step (![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) (by decide) i 1 Qi S
        S C hi (by omega) (by omega) (fun _ => 0) A2 (fun _ => rfl)
        (by simp [f2' 0 (by decide) (by decide), E1, h0]) (by simp [f2' 5 (by decide) (by decide), E1])
        (by
          intro j h2 h8
          have hv := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 →
            (![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) k ≠ 6 ∧ (![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) k ≠ 7 ∧
            (![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) k ≠ 5 ∧
            2 ≤ ((![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) k).val ∧
            ((![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) k).val < 13 by decide) j h2 h8
          obtain ⟨a, b, c, d, e⟩ := hv
          rw [f2' _ a b, hE1, Function.update_of_ne c]; exact hscr _ d e)
        (by simp [f2' 13 (by decide) (by decide), E1, h13])
      replace a3 : A3 3 = ZeroPadding.pad S (List.replicate (i - 1) true) := a3
      have f3' : ∀ z : Fin 14, z.val < 3 ∨ z.val = 4 ∨ z.val = 5 ∨ z.val = 6 ∨ z.val = 7 ∨ z.val = 13 →
          A3 z = A2 z := by
        intro z hz
        apply f3
        intro j h2 h8 e
        have hv := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 →
          ((![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) k).val = 3 ∨
          (8 ≤ ((![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) k).val ∧
            ((![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14) k).val < 13) by decide) j h2 h8
        rw [e] at hv
        omega
      set A4 := Function.update A3 2 (ZeroPadding.pad S [true]) with hA4
      have c1 := const_step [true] (2 : Fin 14) 13 (by decide) S C (by simp; omega) (fun _ => 0) A3 rfl rfl
        (by rw [f3' 2 (by decide), f2' 2 (by decide) (by decide)]; simp [E1, hscr 2 (by decide) (by decide)])
        (by rw [f3' 13 (by decide), f2' 13 (by decide) (by decide)]; simp [E1, h13])
      have c2 := const_step [true] (4 : Fin 14) 13 (by decide) S C (by simp; omega) (fun _ => 0) A4 rfl rfl
        (by simp [A4]; rw [f3' 4 (by decide), f2' 4 (by decide) (by decide)]; simp [E1, hscr 4 (by decide) (by decide)])
        (by simp [A4]; rw [f3' 13 (by decide), f2' 13 (by decide) (by decide)]; simp [E1, h13])
      have n1 := s3.seq (c1.seq c2)
      have sw1 := CloseoutRowsOriginalSwitch.true_run neg1L (CloseoutRowsOriginalSwitch.stop 14) (6 : Fin 14) n1
        (by show readTapeBit (A2 6) 0 = true; rw [a6, read_flag]; exact decide_eq_true hi)
      have sw := CloseoutRowsOriginalSwitch.true_run negL posL (1 : Fin 14) (s1.seq (s2.seq sw1))
        (by show readTapeBit (E 1) 0 = true; rw [h1, read_flag])
      have hne : ¬ (i = 0) := by omega
      refine ⟨_, sw.enlarge (by unfold partCost testCost subCost; simp; omega), by simp [A4, pOf, hne], ?_, by simp [A4, sOf, hne],
        ?_, ?_, ?_⟩
      · simp [A4, iOf, a3]
      · simp [A4]; rw [f3' 0 (by decide), f2' 0 (by decide) (by decide)]; simp [E1]
      · simp [A4]; rw [f3' 1 (by decide), f2' 1 (by decide) (by decide)]; simp [E1]
      · simp [A4]; rw [f3' 13 (by decide), f2' 13 (by decide) (by decide)]; simp [E1]
    · have hi0 : i = 0 := by omega
      have sw1 := CloseoutRowsOriginalSwitch.false_run neg1L (CloseoutRowsOriginalSwitch.stop 14) (6 : Fin 14)
        (show Step (CloseoutRowsOriginalSwitch.stop 14) 0 (fun _ => 0) A2 (fun _ => 0) A2 from ⟨_, rfl, rfl, rfl, le_refl _⟩)
        (by show readTapeBit (A2 6) 0 = false; rw [a6, read_flag]; exact decide_eq_false hi)
      have sw := CloseoutRowsOriginalSwitch.true_run negL posL (1 : Fin 14) (s1.seq (s2.seq sw1))
        (by show readTapeBit (E 1) 0 = true; rw [h1, read_flag])
      refine ⟨_, sw.enlarge (by unfold partCost testCost; simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [f2' 2 (by decide) (by decide)]; simp [E1, pOf, hi0, hscr 2 (by decide) (by decide), pad_ff S hS1]
      · rw [f2' 3 (by decide) (by decide)]; simp [E1, iOf, hi0, hscr 3 (by decide) (by decide), pad_nil']
      · rw [f2' 4 (by decide) (by decide)]; simp [E1, sOf, hi0, hscr 4 (by decide) (by decide), pad_ff S hS1]
      · rw [f2' 0 (by decide) (by decide)]; simp [E1]
      · rw [f2' 1 (by decide) (by decide)]; simp [E1]
      · rw [f2' 13 (by decide) (by decide)]; simp [E1]

/-- **The part decode docked** by any injective map whose private ports lie in `[lo, hi)`; log on `5`. -/
theorem partI (sl : Fin 14 → Fin 128) (hsl : Function.Injective sl) (lo hi : Nat)
    (hfp : ∀ j : Fin 14, 2 ≤ j.val → j.val < 13 → lo ≤ (sl j).val ∧ (sl j).val < hi)
    (n : Bool) (i Qi Qn S C : Nat) (A : Fin 128 → List Bool)
    (h0 : A (sl 0) = ZeroPadding.pad Qi (List.replicate i true)) (h1 : A (sl 1) = ZeroPadding.pad Qn [n])
    (hscr : ∀ j : Fin 14, 2 ≤ j.val → j.val < 13 → A (sl j) = List.replicate S false)
    (h13 : A (sl 13) = List.replicate C false) (hS : partCost i + 1 ≤ S) (hC : partCost i ≤ C) :
    ∃ A' : Fin 128 → List Bool, Step (RecoveryFocus.machine sl partL) (partCost i) (fun _ => 0) A (fun _ => 0) A' ∧
      A' (sl 2) = ZeroPadding.pad S [pOf n i] ∧ A' (sl 3) = ZeroPadding.pad S (List.replicate (iOf n i) true) ∧
      A' (sl 4) = ZeroPadding.pad S [sOf n i] ∧
      (∀ z : Fin 128, z.val < lo ∨ hi ≤ z.val → A' z = A z) ∧ LenOK S A A' := by
  obtain ⟨E', st, e2, e3, e4, e0, e1, e13⟩ := part_run n i Qi Qn S C (fun j => A (sl j)) h0 h1 hscr h13 hS hC
  have keep : ∀ j : Fin 14, ¬ (2 ≤ j.val ∧ j.val < 13) → E' j = A (sl j) := by
    intro j hj
    have hv : j.val = 0 ∨ j.val = 1 ∨ j.val = 13 := by have := j.isLt; omega
    rcases hv with hv | hv | hv
    · rw [show j = 0 from Fin.ext hv]; exact e0
    · rw [show j = 1 from Fin.ext hv]; exact e1
    · rw [show j = 13 from Fin.ext hv]; exact e13
  refine ⟨install sl A E', TermSeg.dock st sl hsl _ A (fun _ => rfl) (fun _ => rfl), ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_slot sl hsl]; exact e2
  · rw [install_slot sl hsl]; exact e3
  · rw [install_slot sl hsl]; exact e4
  · intro z hz
    by_cases hp : ∃ j, sl j = z
    · obtain ⟨j, rfl⟩ := hp
      rw [install_slot sl hsl]
      by_cases hj : 2 ≤ j.val ∧ j.val < 13
      · have := hfp j hj.1 hj.2; omega
      · exact keep j hj
    · exact install_other sl A E' z (fun j e => hp ⟨j, e⟩)
  · intro z
    by_cases hp : ∃ j, sl j = z
    · obtain ⟨j, rfl⟩ := hp
      rw [install_slot sl hsl]
      by_cases hj : 2 ≤ j.val ∧ j.val < 13
      · right
        exact P1Closure.LocalSupport.step_fits st j S (by show (A (sl j)).length ≤ S; rw [hscr j hj.1 hj.2]; simp)
          (by show 0 + partCost i + 1 ≤ S; omega)
      · left; exact keep j hj
    · left; exact install_other sl A E' z (fun j e => hp ⟨j, e⟩)

/-! ## The tail: placement then multiplier (common layout; parts on `60/61/62` and `71/72/73`) -/

def placeW : Bool → Bool → Nat → Nat → List Wr
  | true, true, iL, iR => [.cp 61 9 iL, .c 7 [true], .cp 72 13 iR, .c 11 [true], .c 12 [true], .c 22 [true, true]]
  | true, false, iL, _ => [.cp 61 9 iL, .c 7 [true], .c 22 [true]]
  | false, true, _, iR => [.cp 72 9 iR, .c 7 [true], .c 8 [true], .c 22 [true]]
  | false, false, _, _ => []

def placeT := CloseoutRowsOriginalSwitch.machine (chainM ((placeW true true 0 0).map Wr.shape)).2
  (chainM ((placeW true false 0 0).map Wr.shape)).2 (71 : Fin 128)
def placeF := CloseoutRowsOriginalSwitch.machine (chainM ((placeW false true 0 0).map Wr.shape)).2
  (chainM ((placeW false false 0 0).map Wr.shape)).2 (71 : Fin 128)
def placeM := CloseoutRowsOriginalSwitch.machine placeT placeF (60 : Fin 128)

def rhoT (c : Bool) := CloseoutRowsOriginalSwitch.machine
  (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c true true)) 23 5)
  (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c true false)) 23 5) (73 : Fin 128)
def rhoF (c : Bool) := CloseoutRowsOriginalSwitch.machine
  (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c false true)) 23 5)
  (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c false false)) 23 5) (73 : Fin 128)
def rhoM (c : Bool) := CloseoutRowsOriginalSwitch.machine (rhoT c) (rhoF c) (62 : Fin 128)

theorem placeW_dst (pL pR : Bool) (iL iR : Nat) : ∀ w ∈ placeW pL pR iL iR, 6 ≤ w.dst.val ∧ w.dst.val < 23 := by
  cases pL <;> cases pR <;> simp [placeW, Wr.dst]

theorem placeW_out (pL pR : Bool) (iL iR S : Nat) (hL : iL ≤ S) (hR : iR ≤ S) (hS : 2 ≤ S) :
    ∀ w ∈ placeW pL pR iL iR, (w.out S).length ≤ S := by
  cases pL <;> cases pR <;> simp [placeW, Wr.out, ZeroPadding.pad_length] <;> omega

/-- **The clause tail** (placement, then the multiplier of cross flag `c`). -/
def tailM (c : Bool) := Composition.machine placeM (rhoM c)

theorem place_run (pL pR : Bool) (iL iR S C : Nat) (A : Fin 128 → List Bool)
    (h60 : A 60 = ZeroPadding.pad S [pL]) (h61 : A 61 = ZeroPadding.pad S (List.replicate iL true))
    (h71 : A 71 = ZeroPadding.pad S [pR]) (h72 : A 72 = ZeroPadding.pad S (List.replicate iR true))
    (hout : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A z = List.replicate S false)
    (h5 : A 5 = List.replicate C false) (hL : iL + 1 ≤ C) (hR : iR + 1 ≤ C) (hC : 16 ≤ C) :
    Step placeM (2 * iL + 2 * iR + 40) (fun _ => 0) A (fun _ => 0) (chainApp S (placeW pL pR iL iR) A) := by
  cases pL <;> cases pR
  · have st := chain_step S C (placeW false false iL iR) A h5 (by simp [placeW, ChainPre])
    have sw := CloseoutRowsOriginalSwitch.false_run (chainM ((placeW false true 0 0).map Wr.shape)).2
      (chainM ((placeW false false 0 0).map Wr.shape)).2 (71 : Fin 128) st
      (by show readTapeBit (A 71) 0 = false; rw [h71, read_flag])
    have sw2 := CloseoutRowsOriginalSwitch.false_run placeT placeF (60 : Fin 128) sw
      (by show readTapeBit (A 60) 0 = false; rw [h60, read_flag])
    exact sw2.enlarge (by simp [chainCost, placeW])
  · have st := chain_step S C (placeW false true iL iR) A h5
      (by simp [placeW, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, h72, hout, ex_pad]; omega)
    have e : (placeW false true iL iR).map Wr.shape = (placeW false true 0 0).map Wr.shape := rfl
    rw [e] at st
    have sw := CloseoutRowsOriginalSwitch.true_run (chainM ((placeW false true 0 0).map Wr.shape)).2
      (chainM ((placeW false false 0 0).map Wr.shape)).2 (71 : Fin 128) st
      (by show readTapeBit (A 71) 0 = true; rw [h71, read_flag])
    have sw2 := CloseoutRowsOriginalSwitch.false_run placeT placeF (60 : Fin 128) sw
      (by show readTapeBit (A 60) 0 = false; rw [h60, read_flag])
    exact sw2.enlarge (by simp [chainCost, placeW, Wr.cost]; omega)
  · have st := chain_step S C (placeW true false iL iR) A h5
      (by simp [placeW, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, h61, hout, ex_pad]; omega)
    have e : (placeW true false iL iR).map Wr.shape = (placeW true false 0 0).map Wr.shape := rfl
    rw [e] at st
    have sw := CloseoutRowsOriginalSwitch.false_run (chainM ((placeW true true 0 0).map Wr.shape)).2
      (chainM ((placeW true false 0 0).map Wr.shape)).2 (71 : Fin 128) st
      (by show readTapeBit (A 71) 0 = false; rw [h71, read_flag])
    have sw2 := CloseoutRowsOriginalSwitch.true_run placeT placeF (60 : Fin 128) sw
      (by show readTapeBit (A 60) 0 = true; rw [h60, read_flag])
    exact sw2.enlarge (by simp [chainCost, placeW, Wr.cost]; omega)
  · have st := chain_step S C (placeW true true iL iR) A h5
      (by simp [placeW, ChainPre, Wr.Pre, Wr.app, Wr.dst, Wr.out, h61, h72, hout, ex_pad]; omega)
    have e : (placeW true true iL iR).map Wr.shape = (placeW true true 0 0).map Wr.shape := rfl
    rw [e] at st
    have sw := CloseoutRowsOriginalSwitch.true_run (chainM ((placeW true true 0 0).map Wr.shape)).2
      (chainM ((placeW true false 0 0).map Wr.shape)).2 (71 : Fin 128) st
      (by show readTapeBit (A 71) 0 = true; rw [h71, read_flag])
    have sw2 := CloseoutRowsOriginalSwitch.true_run placeT placeF (60 : Fin 128) sw
      (by show readTapeBit (A 60) 0 = true; rw [h60, read_flag])
    exact sw2.enlarge (by simp [chainCost, placeW, Wr.cost]; omega)

theorem rho_run (c sL sR : Bool) (S C : Nat) (A : Fin 128 → List Bool)
    (h62 : A 62 = ZeroPadding.pad S [sL]) (h73 : A 73 = ZeroPadding.pad S [sR])
    (h23 : A 23 = List.replicate S false) (h5 : A 5 = List.replicate C false) (hC : 16 ≤ C) :
    Step (rhoM c) 40 (fun _ => 0) A (fun _ => 0)
      (Function.update A 23 (ZeroPadding.pad S (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c sL sR)))) := by
  have st := const_step (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c sL sR)) (23 : Fin 128) 5 (by decide)
    S C (by rw [rec_len]; omega) (fun _ => 0) A rfl rfl h23 h5
  have hc : 2 * (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c sL sR)).length + 2 + 2 + 2 ≤ 40 := by
    rw [rec_len]; decide
  cases sL <;> cases sR
  · exact (CloseoutRowsOriginalSwitch.false_run (rhoT c) (rhoF c) (62 : Fin 128)
      (CloseoutRowsOriginalSwitch.false_run _ _ (73 : Fin 128) st
        (by show readTapeBit (A 73) 0 = false; rw [h73, read_flag]))
      (by show readTapeBit (A 62) 0 = false; rw [h62, read_flag])).enlarge hc
  · exact (CloseoutRowsOriginalSwitch.false_run (rhoT c) (rhoF c) (62 : Fin 128)
      (CloseoutRowsOriginalSwitch.true_run _ _ (73 : Fin 128) st
        (by show readTapeBit (A 73) 0 = true; rw [h73, read_flag]))
      (by show readTapeBit (A 62) 0 = false; rw [h62, read_flag])).enlarge hc
  · exact (CloseoutRowsOriginalSwitch.true_run (rhoT c) (rhoF c) (62 : Fin 128)
      (CloseoutRowsOriginalSwitch.false_run _ _ (73 : Fin 128) st
        (by show readTapeBit (A 73) 0 = false; rw [h73, read_flag]))
      (by show readTapeBit (A 62) 0 = true; rw [h62, read_flag])).enlarge hc
  · exact (CloseoutRowsOriginalSwitch.true_run (rhoT c) (rhoF c) (62 : Fin 128)
      (CloseoutRowsOriginalSwitch.true_run _ _ (73 : Fin 128) st
        (by show readTapeBit (A 73) 0 = true; rw [h73, read_flag]))
      (by show readTapeBit (A 62) 0 = true; rw [h62, read_flag])).enlarge hc

/-- **The tail's run**: the cursor outputs of `clauseRec c pL pR iL iR sL sR`. -/
theorem tail_run (c pL pR sL sR : Bool) (iL iR S C : Nat) (A : Fin 128 → List Bool)
    (h60 : A 60 = ZeroPadding.pad S [pL]) (h61 : A 61 = ZeroPadding.pad S (List.replicate iL true))
    (h62 : A 62 = ZeroPadding.pad S [sL])
    (h71 : A 71 = ZeroPadding.pad S [pR]) (h72 : A 72 = ZeroPadding.pad S (List.replicate iR true))
    (h73 : A 73 = ZeroPadding.pad S [sR])
    (hout : ∀ z : Fin 128, 6 ≤ z.val → z.val < 24 → A z = List.replicate S false)
    (h5 : A 5 = List.replicate C false) (hL : iL + 2 ≤ S) (hR : iR + 2 ≤ S) (hLC : iL + 1 ≤ C) (hRC : iR + 1 ≤ C)
    (hS : 16 ≤ S) (hC : 16 ≤ C) :
    ∃ E' : Fin 128 → List Bool, Step (tailM c) (2 * iL + 2 * iR + 81) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (some (clauseRec c pL pR iL iR sL sR)) S E' ∧
      (∀ z : Fin 128, z.val < 6 ∨ 24 ≤ z.val → E' z = A z) ∧ LenOK S A E' := by
  have hS1 : 1 ≤ S := by omega
  have s1 := place_run pL pR iL iR S C A h60 h61 h71 h72 hout h5 hLC hRC hC
  set B := chainApp S (placeW pL pR iL iR) A with hB
  have hBo : ∀ z : Fin 128, z.val < 6 ∨ 24 ≤ z.val → B z = A z := by
    intro z hz
    rw [hB]
    apply chainApp_other
    intro w hw e
    have := placeW_dst pL pR iL iR w hw
    rw [e] at this
    omega
  have hB23 : B 23 = List.replicate S false := by
    rw [hB, chainApp_other S _ A 23 (by
      intro w hw e
      have := placeW_dst pL pR iL iR w hw
      rw [e] at this
      exact absurd this.2 (by decide))]
    exact hout 23 (by decide) (by decide)
  have s2 := rho_run c sL sR S C B (by rw [hBo 62 (by decide)]; exact h62) (by rw [hBo 73 (by decide)]; exact h73)
    hB23 (by rw [hBo 5 (by decide)]; exact h5) hC
  refine ⟨_, (s1.seq s2).enlarge (by omega), ?_, ?_, ?_⟩
  · cases pL <;> cases pR <;>
      apply cursorOut_of <;>
      simp [hB, placeW, chainApp, Wr.app, Wr.dst, Wr.out, clauseRec, facAt, fSys, fTerm, fSide, fIdx, kOf, rhoOf,
        hout, pad_ff S hS1, pad_zero, pad_nil']
  · intro z hz
    have n23 : z ≠ 23 := fun e => by rw [e] at hz; simp at hz
    rw [Function.update_of_ne n23]; exact hBo z hz
  · exact (LenOK.chain _ A (placeW_out pL pR iL iR S (by omega) (by omega) (by omega))).trans
      (LenOK.update B 23 _ (by rw [rec_len]; omega))

end
end NearCubicWires.SourceRequest.CurClause

