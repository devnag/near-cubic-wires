import Proof.SourceAssembly.SourceRequestCurClausePart

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
open NearCubicWires.SourceFactorSel.Count (read_flag sumM wordM mulM sum_step word0_step mul_step flag_unary)
noncomputable section

/-! ## The machine -/

def sL0 : Fin 14 → Fin 128 := ![0, 3, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 5]
def sR28 : Fin 14 → Fin 128 := ![28, 4, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 5]
def sL46 : Fin 14 → Fin 128 := ![46, 3, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 5]
def sR47 : Fin 14 → Fin 128 := ![47, 4, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 5]
def tA : Fin 5 → Fin 128 := ![24, 0, 26, 27, 5]
def sY1 : Fin 9 → Fin 128 := ![0, 24, 28, 29, 30, 31, 32, 33, 5]
def tB : Fin 5 → Fin 128 := ![25, 28, 34, 35, 5]
def sY2 : Fin 9 → Fin 128 := ![28, 25, 36, 37, 38, 39, 40, 41, 5]
def tC : Fin 5 → Fin 128 := ![43, 36, 44, 45, 5]
def dX : Fin 11 → Fin 128 := ![36, 42, 46, 47, 48, 49, 50, 51, 52, 53, 5]

def litLM := Composition.machine (RecoveryFocus.machine sL0 partL) (tailM false)
def litRM := Composition.machine (RecoveryFocus.machine sR28 partL) (tailM false)
def endCM := constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5
def cross2M := Composition.machine (divmodM dX) (Composition.machine (RecoveryFocus.machine sL46 partL)
  (Composition.machine (RecoveryFocus.machine sR47 partL) (tailM true)))
def crossM := Composition.machine (subM sY2) (Composition.machine (wordM false (25 : Fin 128) 42 5)
  (Composition.machine (mulM (24 : Fin 128) 42 43 5) (Composition.machine (testM tC)
    (CloseoutRowsOriginalSwitch.machine endCM cross2M (44 : Fin 128)))))
def restM := Composition.machine (subM sY1) (Composition.machine (testM tB)
  (CloseoutRowsOriginalSwitch.machine crossM litRM (34 : Fin 128)))
/-- **The clause cursor** (ONE fixed machine on the common layout). -/
def clauseM := Composition.machine (sumM (1 : Fin 128) 3 24 5) (Composition.machine (sumM (2 : Fin 128) 4 25 5)
  (Composition.machine (testM tA) (CloseoutRowsOriginalSwitch.machine restM litLM (26 : Fin 128))))

/-! ## Sizes -/

theorem clauseSizes (JL JR : Nat) (nL nR : Bool) :
    JL + nL.toNat ≤ JL + JR + 2 ∧ JR + nR.toNat ≤ JL + JR + 2 ∧
    (JL + nL.toNat) * (JR + nR.toNat) ≤ (JL + JR + 2) * (JL + JR + 2) ∧
    JL + JR + 2 ≤ (JL + JR + 2) * (JL + JR + 2) ∧
    (JL + JR + 2) * (JL + JR + 2) ≤ (JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2)) ∧
    16 ≤ (JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2)) ∧
    curBig JL JR = 64 * ((JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2))) := by
  have b1 : nL.toNat ≤ 1 := Bool.toNat_le nL
  have b2 : nR.toNat ≤ 1 := Bool.toNat_le nR
  have hM : 2 ≤ JL + JR + 2 := by omega
  have h1 : JL + nL.toNat ≤ JL + JR + 2 := by omega
  have h2 : JR + nR.toNat ≤ JL + JR + 2 := by omega
  obtain ⟨p1, p2, p3, p4, p5⟩ := SourceFactorSel.Count.pow_facts (JL + JR + 2) (JL + JR + 2) le_rfl hM
  refine ⟨h1, h2, Nat.mul_le_mul h1 h2, Nat.le_mul_of_pos_left _ (by omega), Nat.le_mul_of_pos_right _ (by positivity),
    p5, rfl⟩

/-! ## The left literal (`m < aL`) -/

theorem litL_run (nL : Bool) (m JL JR Qm Qf S C : Nat) (E A : Fin 128 → List Bool)
    (hm : m < JL + nL.toNat) (hS : curBig JL JR ≤ S) (hC : curBig JL JR ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qm (List.replicate m true)) (h3 : E 3 = ZeroPadding.pad Qf [nL])
    (h5 : E 5 = List.replicate C false) (hscr : ∀ j : Fin 128, 6 ≤ j.val → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 28 ≤ z.val → A z = E z) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step litLM (curBig JL JR) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (some (litEntry nL false m)) S E' ∧ (∀ j : Fin 128, j.val < 6 → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, hbig⟩ := clauseSizes JL JR nL false
  have hS1 : 1 ≤ S := by omega
  obtain ⟨A1, s1, a60, a61, a62, f1, l1⟩ := partI sL0 (by decide) 60 71 (by decide) nL m Qm Qf S C A
    (by simp [sL0, hk 0 (by decide), h0]) (by simp [sL0, hk 3 (by decide), h3])
    (by
      intro j h2 h13
      have hv := (show ∀ k : Fin 14, 2 ≤ k.val → k.val < 13 → 60 ≤ (sL0 k).val ∧ (sL0 k).val < 71 by decide) j h2 h13
      rw [hk _ (by omega)]; exact hscr _ (by omega))
    (by simp [sL0, hk 5 (by decide), h5]) (by unfold partCost; omega) (by unfold partCost; omega)
  have bl : ∀ z : Fin 128, 6 ≤ z.val → z.val < 60 ∨ 71 ≤ z.val → z.val < 24 ∨ 28 ≤ z.val →
      A1 z = List.replicate S false := fun z h6 h1 h2 => (f1 z h1).trans ((hk z h2).trans (hscr z h6))
  obtain ⟨E', s2, ho, hk2, l2⟩ := tail_run false (pOf nL m) false (sOf nL m) false (iOf nL m) 0 S C A1 a60 a61 a62
    (by rw [bl 71 (by decide) (by decide) (by decide)]; exact (pad_ff S hS1).symm)
    (by rw [bl 72 (by decide) (by decide) (by decide)]; exact (pad_zero S).symm)
    (by rw [bl 73 (by decide) (by decide) (by decide)]; exact (pad_ff S hS1).symm)
    (fun z h6 h24 => bl z h6 (by omega) (by omega)) (by rw [f1 5 (by decide), hk 5 (by decide)]; exact h5)
    (by unfold iOf; omega) (by omega) (by unfold iOf; omega) (by omega) (by omega) (by omega)
  refine ⟨E', (s1.seq s2).enlarge ?_, ?_, ?_, L.trans (l1.trans l2)⟩
  · unfold partCost iOf; omega
  · rw [lit_as_rec_L]; exact ho
  · intro j hj
    rw [hk2 j (Or.inl hj), f1 j (by omega), hk j (by omega)]

/-! ## The right literal (`aL ≤ m`, `m - aL < aR`) -/

theorem litR_run (nR : Bool) (y JL JR Qf S C : Nat) (E A : Fin 128 → List Bool)
    (hy : y < JR + nR.toNat) (hS : curBig JL JR ≤ S) (hC : curBig JL JR ≤ C)
    (h4 : E 4 = ZeroPadding.pad Qf [nR])
    (h5 : E 5 = List.replicate C false) (hscr : ∀ j : Fin 128, 6 ≤ j.val → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 36 ≤ z.val → A z = E z)
    (h28 : A 28 = ZeroPadding.pad S (List.replicate y true)) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step litRM (curBig JL JR) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (some (litEntry nR true y)) S E' ∧ (∀ j : Fin 128, j.val < 6 → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, hbig⟩ := clauseSizes JL JR false nR
  have hS1 : 1 ≤ S := by omega
  obtain ⟨A1, s1, a71, a72, a73, f1, l1⟩ := partI sR28 (by decide) 71 82 (by decide) nR y S Qf S C A
    (by simp [sR28, h28]) (by simp [sR28, hk 4 (by decide), h4])
    (by
      intro j h2 h13
      have hv := (show ∀ k : Fin 14, 2 ≤ k.val → k.val < 13 → 71 ≤ (sR28 k).val ∧ (sR28 k).val < 82 by decide) j h2 h13
      rw [hk _ (by omega)]; exact hscr _ (by omega))
    (by simp [sR28, hk 5 (by decide), h5]) (by unfold partCost; omega) (by unfold partCost; omega)
  have bl : ∀ z : Fin 128, 6 ≤ z.val → z.val < 71 ∨ 82 ≤ z.val → z.val < 24 ∨ 36 ≤ z.val →
      A1 z = List.replicate S false := fun z h6 h1 h2 => (f1 z h1).trans ((hk z h2).trans (hscr z h6))
  obtain ⟨E', s2, ho, hk2, l2⟩ := tail_run false false (pOf nR y) false (sOf nR y) 0 (iOf nR y) S C A1
    (by rw [bl 60 (by decide) (by decide) (by decide)]; exact (pad_ff S hS1).symm)
    (by rw [bl 61 (by decide) (by decide) (by decide)]; exact (pad_zero S).symm)
    (by rw [bl 62 (by decide) (by decide) (by decide)]; exact (pad_ff S hS1).symm)
    a71 a72 a73
    (fun z h6 h24 => bl z h6 (by omega) (by omega)) (by rw [f1 5 (by decide), hk 5 (by decide)]; exact h5)
    (by omega) (by unfold iOf; omega) (by omega) (by unfold iOf; omega) (by omega) (by omega)
  refine ⟨E', (s1.seq s2).enlarge ?_, ?_, ?_, L.trans (l1.trans l2)⟩
  · unfold partCost iOf; omega
  · rw [lit_as_rec_R]; exact ho
  · intro j hj
    rw [hk2 j (Or.inl hj), f1 j (by omega), hk j (by omega)]

/-! ## The cross block (`y = m - aL - aR < aL·aR`) -/

theorem cross2_run (nL nR : Bool) (y JL JR Qf S C : Nat) (E A : Fin 128 → List Bool)
    (hy : y < (JL + nL.toNat) * (JR + nR.toNat)) (hS : curBig JL JR ≤ S) (hC : curBig JL JR ≤ C)
    (h3 : E 3 = ZeroPadding.pad Qf [nL]) (h4 : E 4 = ZeroPadding.pad Qf [nR])
    (h5 : E 5 = List.replicate C false) (hscr : ∀ j : Fin 128, 6 ≤ j.val → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 46 ≤ z.val → A z = E z)
    (h36 : A 36 = ZeroPadding.pad S (List.replicate y true))
    (h42 : A 42 = ZeroPadding.pad S (CompareMachine.word (JR + nR.toNat))) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step cross2M (2 * curBig JL JR) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (some (crossEntry nL nR (y / (JR + nR.toNat)) (y % (JR + nR.toNat)))) S E' ∧
      (∀ j : Fin 128, j.val < 6 → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, hbig⟩ := clauseSizes JL JR nL nR
  have hS1 : 1 ≤ S := by omega
  set aR := JR + nR.toNat with haR
  have haR0 : 0 < aR := by
    rcases Nat.eq_zero_or_pos aR with h | h
    · rw [h] at hy; simp at hy
    · exact h
  have hyl : y ≤ (JL + JR + 2) * (JL + JR + 2) := by omega
  have hq : y / aR < JL + nL.toNat := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hy)
  have hr : y % aR < aR := Nat.mod_lt _ haR0
  obtain ⟨A1, s1, a46, a47, f1, l1⟩ := divI dX (by decide) 46 54 (by decide) y aR S S S C haR0 (by omega) (by omega)
    (by omega) A (by simp [dX, h36]) (by simp [dX, h42])
    (by
      intro j h2 h10
      have hv := vals11 dX 46 54 (by decide) j h2 h10
      rw [hk _ (by omega)]; exact hscr _ (by omega))
    (by simp [dX, hk 5 (by decide), h5])
  replace a46 : A1 46 = ZeroPadding.pad S (List.replicate (y / aR) true) := a46
  replace a47 : A1 47 = ZeroPadding.pad S (List.replicate (y % aR) true) := a47
  have k1 : ∀ z : Fin 128, z.val < 24 ∨ 54 ≤ z.val → A1 z = E z := fun z hz => (f1 z (by omega)).trans (hk z (by omega))
  obtain ⟨A2, s2, a60, a61, a62, f2, l2⟩ := partI sL46 (by decide) 60 71 (by decide) nL (y / aR) S Qf S C A1
    (by simp [sL46, a46]) (by simp [sL46, k1 3 (by decide), h3])
    (by
      intro j h2 h13
      have hv := (show ∀ k : Fin 14, 2 ≤ k.val → k.val < 13 → 60 ≤ (sL46 k).val ∧ (sL46 k).val < 71 by decide) j h2 h13
      rw [k1 _ (by omega)]; exact hscr _ (by omega))
    (by simp [sL46, k1 5 (by decide), h5]) (by unfold partCost; omega) (by unfold partCost; omega)
  have hA2_47 : A2 47 = ZeroPadding.pad S (List.replicate (y % aR) true) := (f2 47 (by decide)).trans a47
  have k2 : ∀ z : Fin 128, z.val < 24 ∨ 71 ≤ z.val → A2 z = E z := fun z hz =>
    (f2 z (by omega)).trans (k1 z (by omega))
  obtain ⟨A3, s3, a71, a72, a73, f3, l3⟩ := partI sR47 (by decide) 71 82 (by decide) nR (y % aR) S Qf S C A2
    (by simp [sR47, hA2_47]) (by simp [sR47, k2 4 (by decide), h4])
    (by
      intro j h2 h13
      have hv := (show ∀ k : Fin 14, 2 ≤ k.val → k.val < 13 → 71 ≤ (sR47 k).val ∧ (sR47 k).val < 82 by decide) j h2 h13
      rw [k2 _ (by omega)]; exact hscr _ (by omega))
    (by simp [sR47, k2 5 (by decide), h5]) (by unfold partCost; omega) (by unfold partCost; omega)
  have hA3_60 : A3 60 = ZeroPadding.pad S [pOf nL (y / aR)] := (f3 60 (by decide)).trans a60
  have hA3_61 : A3 61 = ZeroPadding.pad S (List.replicate (iOf nL (y / aR)) true) := (f3 61 (by decide)).trans a61
  have hA3_62 : A3 62 = ZeroPadding.pad S [sOf nL (y / aR)] := (f3 62 (by decide)).trans a62
  have k3 : ∀ z : Fin 128, z.val < 24 ∨ 82 ≤ z.val → A3 z = E z := fun z hz =>
    (f3 z (by omega)).trans (k2 z (by omega))
  obtain ⟨E', s4, ho, hk4, l4⟩ := tail_run true (pOf nL (y / aR)) (pOf nR (y % aR)) (sOf nL (y / aR))
    (sOf nR (y % aR)) (iOf nL (y / aR)) (iOf nR (y % aR)) S C A3 hA3_60 hA3_61 hA3_62 a71 a72 a73
    (fun z h6 h24 => (k3 z (by omega)).trans (hscr z h6)) (by rw [k3 5 (by decide)]; exact h5)
    (by unfold iOf; omega) (by unfold iOf; omega) (by unfold iOf; omega) (by unfold iOf; omega) (by omega) (by omega)
  refine ⟨E', (s1.seq (s2.seq (s3.seq s4))).enlarge ?_, ?_, ?_, L.trans (l1.trans (l2.trans (l3.trans l4)))⟩
  · unfold divmodCost partCost iOf; omega
  · rw [cross_as_rec]; exact ho
  · intro j hj
    rw [hk4 j (Or.inl hj)]; exact k3 j (by omega)

/-! ## Blocks 2–end (`aL ≤ m`, `aR ≤ m - aL`) -/

theorem cross_run (nL nR : Bool) (m JL JR Qf S C : Nat) (E A : Fin 128 → List Bool)
    (hb1 : JL + nL.toNat ≤ m) (hb2 : JR + nR.toNat ≤ m - (JL + nL.toNat))
    (hm : m ≤ (JL + nL.toNat) + ((JR + nR.toNat) + (JL + nL.toNat) * (JR + nR.toNat)))
    (hS : curBig JL JR ≤ S) (hC : curBig JL JR ≤ C)
    (h3 : E 3 = ZeroPadding.pad Qf [nL]) (h4 : E 4 = ZeroPadding.pad Qf [nR])
    (h5 : E 5 = List.replicate C false) (hscr : ∀ j : Fin 128, 6 ≤ j.val → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 36 ≤ z.val → A z = E z)
    (h24 : A 24 = ZeroPadding.pad S (List.replicate (JL + nL.toNat) true))
    (h25 : A 25 = ZeroPadding.pad S (List.replicate (JR + nR.toNat) true))
    (h28 : A 28 = ZeroPadding.pad S (List.replicate (m - (JL + nL.toNat)) true)) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step crossM (4 * curBig JL JR) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (selAt .clause false false nL nR JL JR m) S E' ∧
      (∀ j : Fin 128, j.val < 6 → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, hbig⟩ := clauseSizes JL JR nL nR
  have hS1 : 1 ≤ S := by omega
  have e1 : (JL + nL.toNat) * (2 * (JR + nR.toNat) + 3) = 2 * ((JL + nL.toNat) * (JR + nR.toNat)) + 3 * (JL + nL.toNat) := by ring
  obtain ⟨A1, s1, a36, f1, l1⟩ := subI sY2 (by decide) 36 42 (by decide) (m - (JL + nL.toNat)) (JR + nR.toNat) S S S C hb2 (by omega)
    (by omega) A (by simp [sY2, h28]) (by simp [sY2, h25])
    (by
      intro j h2 h8
      have hv := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 → 36 ≤ (sY2 k).val ∧ (sY2 k).val < 42 by decide) j h2 h8
      rw [hk _ (by omega)]; exact hscr _ (by omega))
    (by simp [sY2, hk 5 (by decide), h5])
  replace a36 : A1 36 = ZeroPadding.pad S (List.replicate (m - (JL + nL.toNat) - (JR + nR.toNat)) true) := a36
  have k1 : ∀ z : Fin 128, z.val < 24 ∨ 42 ≤ z.val → A1 z = E z := fun z hz => (f1 z (by omega)).trans (hk z (by omega))
  have hA1_24 : A1 24 = ZeroPadding.pad S (List.replicate (JL + nL.toNat) true) := (f1 24 (by decide)).trans h24
  have hA1_25 : A1 25 = ZeroPadding.pad S (List.replicate (JR + nR.toNat) true) := (f1 25 (by decide)).trans h25
  set A2 := Function.update A1 42 (ZeroPadding.pad S (CompareMachine.word (JR + nR.toNat))) with hA2
  have s2 := word0_step (25 : Fin 128) 42 5 (by decide) (by decide) (by decide) (JR + nR.toNat) S S C (by omega) (by omega)
    (fun _ => 0) A1 (fun _ _ => rfl) hA1_25 (by rw [k1 42 (by decide)]; exact hscr 42 (by decide))
    (by rw [k1 5 (by decide)]; exact h5)
  set A3 := Function.update A2 43 (ZeroPadding.pad S (List.replicate ((JL + nL.toNat) * (JR + nR.toNat)) true)) with hA3
  have s3 := mul_step (24 : Fin 128) 42 43 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (JL + nL.toNat) (JR + nR.toNat) S S S C (by rw [e1]; omega) (fun _ => 0) A2 (fun _ _ => rfl) (by simp [A2, hA1_24]) (by simp [A2])
    (by simp [A2, k1 43 (by decide), hscr 43 (by decide)]) (by simp [A2, k1 5 (by decide), h5])
  obtain ⟨A4, s4, a44, f4, l4⟩ := testI tC (by decide) 44 46 (by decide) ((JL + nL.toNat) * (JR + nR.toNat)) (m - (JL + nL.toNat) - (JR + nR.toNat)) S S S C (by omega)
    (by omega) A3 (by simp [tC, A3]) (by simp [tC, A2, A3, a36])
    (by simp [tC, A2, A3, k1 44 (by decide), hscr 44 (by decide)])
    (by simp [tC, A2, A3, k1 45 (by decide), hscr 45 (by decide)]) (by simp [tC, A2, A3, k1 5 (by decide), h5])
  replace a44 : A4 44 = ZeroPadding.pad S [decide ((JL + nL.toNat) * (JR + nR.toNat) ≤ m - (JL + nL.toNat) - (JR + nR.toNat))] := a44
  have hA4_36 : A4 36 = ZeroPadding.pad S (List.replicate (m - (JL + nL.toNat) - (JR + nR.toNat)) true) := by
    rw [f4 36 (by decide)]; simp [A2, A3, a36]
  have hA4_42 : A4 42 = ZeroPadding.pad S (CompareMachine.word (JR + nR.toNat)) := by rw [f4 42 (by decide)]; simp [A2, A3]
  have k4 : ∀ z : Fin 128, z.val < 24 ∨ 46 ≤ z.val → A4 z = E z := by
    intro z hz
    have n42 : z ≠ 42 := fun e => by rw [e] at hz; exact absurd hz (by decide)
    have n43 : z ≠ 43 := fun e => by rw [e] at hz; exact absurd hz (by decide)
    rw [f4 z (by omega), hA3, Function.update_of_ne n43, hA2, Function.update_of_ne n42]; exact k1 z (by omega)
  have L4 : LenOK S E A4 := L.trans (l1.trans (((LenOK.update A1 42 _ (by simp [CompareMachine.word]; omega)).trans
    (LenOK.update A2 43 _ (by simp; omega))).trans l4))
  by_cases hb3 : (JL + nL.toNat) * (JR + nR.toNat) ≤ m - (JL + nL.toNat) - (JR + nR.toNat)
  · -- past the end
    set E' := Function.update A4 23 (ZeroPadding.pad S (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0))
      with hE'
    have s5 := const_step (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5 (by decide) S C
      (by rw [rec_len]; omega) (fun _ => 0) A4 rfl rfl
      (by rw [k4 23 (by decide)]; exact hscr 23 (by decide)) (by rw [k4 5 (by decide)]; exact h5)
    have sw := CloseoutRowsOriginalSwitch.true_run endCM cross2M (44 : Fin 128) s5
      (by show readTapeBit (A4 44) 0 = true; rw [a44, read_flag]; exact decide_eq_true hb3)
    refine ⟨E', (s1.seq (s2.seq (s3.seq (s4.seq sw)))).enlarge ?_, ?_, ?_, ?_⟩
    · rw [hbig]; unfold subCost testCost; rw [rec_len, e1]; omega
    · rw [clause_end false false nL nR JL JR m (by omega)]
      have b : ∀ z : Fin 128, 6 ≤ z.val → z.val < 23 → E' z = List.replicate S false := by
        intro z h6 h23
        have n23 : z ≠ 23 := fun e => by rw [e] at h23; exact absurd h23 (by decide)
        rw [hE', Function.update_of_ne n23, k4 z (by omega)]; exact hscr z h6
      apply cursorOut_of <;> first
        | (rw [b _ (by decide) (by decide)]; simp [facAt, fSys, fTerm, fSide, fIdx, kOf, pad_ff S hS1, pad_nil'])
        | simp [hE', rhoOf]
    · intro j hj
      have n23 : j ≠ 23 := fun e => by rw [e] at hj; exact absurd hj (by decide)
      rw [hE', Function.update_of_ne n23]; exact k4 j (by omega)
    · exact L4.trans (LenOK.update A4 23 _ (by rw [rec_len]; omega))
  · have hy : m - (JL + nL.toNat) - (JR + nR.toNat) < (JL + nL.toNat) * (JR + nR.toNat) := Nat.lt_of_not_le hb3
    obtain ⟨E', st, ho, hke, hl⟩ := cross2_run nL nR (m - (JL + nL.toNat) - (JR + nR.toNat)) JL JR Qf S C E A4 hy hS hC h3 h4 h5 hscr k4
      hA4_36 hA4_42 L4
    have sw := CloseoutRowsOriginalSwitch.false_run endCM cross2M (44 : Fin 128) st
      (by show readTapeBit (A4 44) 0 = false; rw [a44, read_flag]; exact decide_eq_false hb3)
    refine ⟨E', (s1.seq (s2.seq (s3.seq (s4.seq sw)))).enlarge ?_, ?_, hke, hl⟩
    · rw [hbig] at *; unfold subCost testCost; rw [e1]; omega
    · rw [clause_cross false false nL nR JL JR m (by omega) (by omega),
        show m - ((JL + nL.toNat) + (JR + nR.toNat)) = m - (JL + nL.toNat) - (JR + nR.toNat) by omega]
      exact ho

/-- Blocks after the left literal (`aL ≤ m`). -/
theorem rest_run (nL nR : Bool) (m JL JR Qm Qf S C : Nat) (E A : Fin 128 → List Bool)
    (hb1 : JL + nL.toNat ≤ m)
    (hm : m ≤ (JL + nL.toNat) + ((JR + nR.toNat) + (JL + nL.toNat) * (JR + nR.toNat)))
    (hS : curBig JL JR ≤ S) (hC : curBig JL JR ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qm (List.replicate m true))
    (h3 : E 3 = ZeroPadding.pad Qf [nL]) (h4 : E 4 = ZeroPadding.pad Qf [nR])
    (h5 : E 5 = List.replicate C false) (hscr : ∀ j : Fin 128, 6 ≤ j.val → E j = List.replicate S false)
    (hk : ∀ z : Fin 128, z.val < 24 ∨ 28 ≤ z.val → A z = E z)
    (h24 : A 24 = ZeroPadding.pad S (List.replicate (JL + nL.toNat) true))
    (h25 : A 25 = ZeroPadding.pad S (List.replicate (JR + nR.toNat) true)) (L : LenOK S E A) :
    ∃ E' : Fin 128 → List Bool, Step restM (8 * curBig JL JR) (fun _ => 0) A (fun _ => 0) E' ∧
      CursorOut (selAt .clause false false nL nR JL JR m) S E' ∧
      (∀ j : Fin 128, j.val < 6 → E' j = E j) ∧ LenOK S E E' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, hbig⟩ := clauseSizes JL JR nL nR
  have hmX : m ≤ 3 * ((JL + JR + 2) * (JL + JR + 2)) := by omega
  obtain ⟨A1, s1, a28, f1, l1⟩ := subI sY1 (by decide) 28 34 (by decide) m (JL + nL.toNat) Qm S S C hb1 (by omega) (by omega) A
    (by simp [sY1, hk 0 (by decide), h0]) (by simp [sY1, h24])
    (by
      intro j h2 h8
      have hv := (show ∀ k : Fin 9, 2 ≤ k.val → k.val < 8 → 28 ≤ (sY1 k).val ∧ (sY1 k).val < 34 by decide) j h2 h8
      rw [hk _ (by omega)]; exact hscr _ (by omega))
    (by simp [sY1, hk 5 (by decide), h5])
  replace a28 : A1 28 = ZeroPadding.pad S (List.replicate (m - (JL + nL.toNat)) true) := a28
  have k1 : ∀ z : Fin 128, z.val < 24 ∨ 34 ≤ z.val → A1 z = E z := fun z hz => (f1 z (by omega)).trans (hk z (by omega))
  have hA1_24 : A1 24 = ZeroPadding.pad S (List.replicate (JL + nL.toNat) true) := (f1 24 (by decide)).trans h24
  have hA1_25 : A1 25 = ZeroPadding.pad S (List.replicate (JR + nR.toNat) true) := (f1 25 (by decide)).trans h25
  obtain ⟨A2, s2, a34, f2, l2⟩ := testI tB (by decide) 34 36 (by decide) (JR + nR.toNat) (m - (JL + nL.toNat)) S S S C (by omega) (by omega) A1
    (by simp [tB, hA1_25]) (by simp [tB, a28]) (by simp [tB, k1 34 (by decide), hscr 34 (by decide)])
    (by simp [tB, k1 35 (by decide), hscr 35 (by decide)]) (by simp [tB, k1 5 (by decide), h5])
  replace a34 : A2 34 = ZeroPadding.pad S [decide ((JR + nR.toNat) ≤ m - (JL + nL.toNat))] := a34
  have k2 : ∀ z : Fin 128, z.val < 24 ∨ 36 ≤ z.val → A2 z = E z := fun z hz => (f2 z (by omega)).trans (k1 z (by omega))
  have hA2_24 : A2 24 = ZeroPadding.pad S (List.replicate (JL + nL.toNat) true) := (f2 24 (by decide)).trans hA1_24
  have hA2_25 : A2 25 = ZeroPadding.pad S (List.replicate (JR + nR.toNat) true) := (f2 25 (by decide)).trans hA1_25
  have hA2_28 : A2 28 = ZeroPadding.pad S (List.replicate (m - (JL + nL.toNat)) true) := (f2 28 (by decide)).trans a28
  have L2 : LenOK S E A2 := L.trans (l1.trans l2)
  by_cases hb2 : (JR + nR.toNat) ≤ m - (JL + nL.toNat)
  · obtain ⟨E', st, ho, hke, hl⟩ := cross_run nL nR m JL JR Qf S C E A2 hb1 hb2 hm hS hC h3 h4 h5 hscr k2 hA2_24
      hA2_25 hA2_28 L2
    have sw := CloseoutRowsOriginalSwitch.true_run crossM litRM (34 : Fin 128) st
      (by show readTapeBit (A2 34) 0 = true; rw [a34, read_flag]; exact decide_eq_true hb2)
    refine ⟨E', (s1.seq (s2.seq sw)).enlarge ?_, ho, hke, hl⟩
    rw [hbig] at *; unfold subCost testCost; omega
  · have hy : m - (JL + nL.toNat) < (JR + nR.toNat) := Nat.lt_of_not_le hb2
    obtain ⟨E', st, ho, hke, hl⟩ := litR_run nR (m - (JL + nL.toNat)) JL JR Qf S C E A2 hy hS hC h4 h5 hscr k2 hA2_28 L2
    have sw := CloseoutRowsOriginalSwitch.false_run crossM litRM (34 : Fin 128) st
      (by show readTapeBit (A2 34) 0 = false; rw [a34, read_flag]; exact decide_eq_false hb2)
    refine ⟨E', (s1.seq (s2.seq sw)).enlarge ?_, ?_, hke, hl⟩
    · rw [hbig] at *; unfold subCost testCost; omega
    · rw [clause_litR false false nL nR JL JR m hb1 hy]; exact ho

/-- **The clause cursor meets the common contract.** -/
theorem clause_cursor : CursorRun clauseM .clause := by
  intro sL sR nL nR m JL JR Qm Q1 Q2 Qf S C E hm hS hC h0 h1 h2 h3 h4 h5 hscr
  replace h0 : E 0 = ZeroPadding.pad Qm (List.replicate m true) := h0
  replace h1 : E 1 = ZeroPadding.pad Q1 (List.replicate JL true) := h1
  replace h2 : E 2 = ZeroPadding.pad Q2 (List.replicate JR true) := h2
  replace h3 : E 3 = ZeroPadding.pad Qf [nL] := h3
  replace h4 : E 4 = ZeroPadding.pad Qf [nR] := h4
  replace h5 : E 5 = List.replicate C false := h5
  have hm' : m ≤ (JL + nL.toNat) + ((JR + nR.toNat) + (JL + nL.toNat) * (JR + nR.toNat)) := by
    have := hm
    simp only [MonomialSpec.siteLen, SourceFactorSel.Count.litLen_eq] at this
    exact this
  obtain ⟨c1, c2, c3, c4, c5, c6, hbig⟩ := clauseSizes JL JR nL nR
  have hS1 : 1 ≤ S := by omega
  have hselL : selAt .clause sL sR nL nR JL JR m = selAt .clause false false nL nR JL JR m := rfl
  set A1 := Function.update E 24 (ZeroPadding.pad S (List.replicate (JL + nL.toNat) true)) with hA1
  have s1 := sum_step (1 : Fin 128) 3 24 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    JL nL.toNat Q1 (max Qf 1) S C (by omega) (fun _ => 0) E (fun _ _ => rfl) h1 (by rw [h3, flag_unary])
    (hscr 24 (by decide)) h5
  set A2 := Function.update A1 25 (ZeroPadding.pad S (List.replicate (JR + nR.toNat) true)) with hA2
  have s2 := sum_step (2 : Fin 128) 4 25 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    JR nR.toNat Q2 (max Qf 1) S C (by omega) (fun _ => 0) A1 (fun _ _ => rfl) (by simp [A1, h2])
    (by simp [A1]; rw [h4, flag_unary]) (by simp [A1, hscr 25 (by decide)]) (by simp [A1, h5])
  obtain ⟨A3, s3, a26, f3, l3⟩ := testI tA (by decide) 26 28 (by decide) (JL + nL.toNat) m S Qm S C (by omega)
    (by omega) A2 (by simp [tA, A1, A2]) (by simp [tA, A1, A2, h0]) (by simp [tA, A1, A2, hscr 26 (by decide)])
    (by simp [tA, A1, A2, hscr 27 (by decide)]) (by simp [tA, A1, A2, h5])
  replace a26 : A3 26 = ZeroPadding.pad S [decide (JL + nL.toNat ≤ m)] := a26
  have k3 : ∀ z : Fin 128, z.val < 24 ∨ 28 ≤ z.val → A3 z = E z := by
    intro z hz
    have n24 : z ≠ 24 := fun e => by rw [e] at hz; exact absurd hz (by decide)
    have n25 : z ≠ 25 := fun e => by rw [e] at hz; exact absurd hz (by decide)
    rw [f3 z (by omega), hA2, Function.update_of_ne n25, hA1, Function.update_of_ne n24]
  have hA3_24 : A3 24 = ZeroPadding.pad S (List.replicate (JL + nL.toNat) true) := by
    rw [f3 24 (by decide)]; simp [A1, A2]
  have hA3_25 : A3 25 = ZeroPadding.pad S (List.replicate (JR + nR.toNat) true) := by
    rw [f3 25 (by decide)]; simp [A2]
  have L3 : LenOK S E A3 :=
    ((LenOK.update E 24 _ (by simp; omega)).trans (LenOK.update A1 25 _ (by simp; omega))).trans l3
  have fin : ∀ E' : Fin 128 → List Bool, LenOK S E E' → ∀ j : Fin 128, 24 ≤ j.val → (E' j).length ≤ S := by
    intro E' hl j hj
    rcases hl j with e | e
    · rw [e, hscr j (by omega)]; simp
    · exact e
  by_cases hb : JL + nL.toNat ≤ m
  · obtain ⟨E', st, ho, hke, hl⟩ := rest_run nL nR m JL JR Qm Qf S C E A3 hb hm' hS hC h0 h3 h4 h5 hscr k3 hA3_24
      hA3_25 L3
    have sw := CloseoutRowsOriginalSwitch.true_run restM litLM (26 : Fin 128) st
      (by show readTapeBit (A3 26) 0 = true; rw [a26, read_flag]; exact decide_eq_true hb)
    refine ⟨E', (s1.seq (s2.seq (s3.seq sw))).enlarge ?_, ?_, hke, fin E' hl⟩
    · unfold curCost; rw [hbig] at *; unfold testCost; omega
    · rw [hselL]; exact ho
  · have hx : m < JL + nL.toNat := Nat.lt_of_not_le hb
    obtain ⟨E', st, ho, hke, hl⟩ := litL_run nL m JL JR Qm Qf S C E A3 hx hS hC h0 h3 h5 hscr k3 L3
    have sw := CloseoutRowsOriginalSwitch.false_run restM litLM (26 : Fin 128) st
      (by show readTapeBit (A3 26) 0 = false; rw [a26, read_flag]; exact decide_eq_false hb)
    refine ⟨E', (s1.seq (s2.seq (s3.seq sw))).enlarge ?_, ?_, hke, fin E' hl⟩
    · unfold curCost; rw [hbig] at *; unfold testCost; omega
    · rw [clause_litL sL sR nL nR JL JR m hx]; exact ho

end
end NearCubicWires.SourceRequest.CurClause

