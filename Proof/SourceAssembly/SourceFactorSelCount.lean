import Proof.SourceAssembly.SourceFactorSelDesc
import Proof.SourceAssembly.SourceRequestMonomialSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Count
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
noncomputable section

/-! ## Primitives -/

theorem sum_local (r s Qa Qb S C : Nat) (hC : r + s + 2 ≤ C) :
    Step ClockUnarySum.machine (2 * (r + s) + 6) (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate r true), ZeroPadding.pad Qb (List.replicate s true),
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate r true), ZeroPadding.pad Qb (List.replicate s true),
        ZeroPadding.pad S (List.replicate (r + s) true), List.replicate C false] := by
  have base := (SLoad.MaskFrame.step_of_clockReady (ClockUnarySum.sum_ready r s)).pad ![Qa, Qb, S, C]
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · rfl
    · rfl
    · exact Desc.pad_nil S
    · exact Desc.pad_nil C
  · funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · show ZeroPadding.pad C (List.replicate (r + s + 2) false) = _
      rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left hC]
      rfl

theorem mul_local (d e Qa Qb S C : Nat) (hC : d * (2 * e + 3) + 2 ≤ C) :
    Step ClockUnaryProduct.machine (2 * (d * (2 * e + 3) + 2) + 2) (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate d true), ZeroPadding.pad Qb (CompareMachine.word e),
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate d true), ZeroPadding.pad Qb (CompareMachine.word e),
        ZeroPadding.pad S (List.replicate (d * e) true), List.replicate C false] := by
  obtain ⟨rc, hrun, t0, t1, t2, t3, hh, hs⟩ := ClockUnaryProduct.product_run d e
  have hin : (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
      ![List.replicate d true, false :: List.replicate e true, []] (fun _ : Fin 1 => [])) =
      (![List.replicate d true, CompareMachine.word e, [], []] : Fin 4 → List Bool) := by
    funext i
    fin_cases i <;> rfl
  rw [hin] at hrun
  have hready : ClockJoin.ReadyRun ClockUnaryProduct.machine (2 * (d * (2 * e + 3) + 2) + 2)
      ![List.replicate d true, CompareMachine.word e, [], []]
      ![List.replicate d true, CompareMachine.word e, List.replicate (d * e) true,
        List.replicate (d * (2 * e + 3) + 2) false] := by
    refine ⟨rc, hrun, ?_, hh, le_of_eq hs⟩
    funext i
    fin_cases i
    · exact t0
    · exact t1
    · exact t2
    · exact t3
  have base := (SLoad.MaskFrame.step_of_clockReady hready).pad ![Qa, Qb, S, C]
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · rfl
    · rfl
    · exact Desc.pad_nil S
    · exact Desc.pad_nil C
  · funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · show ZeroPadding.pad C (List.replicate (d * (2 * e + 3) + 2) false) = _
      rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left hC]
      rfl

theorem word_local (x : Bool) (n Qa R C : Nat) (hR : n + x.toNat + 2 ≤ R) (hC : n + 3 ≤ C) :
    Step (DimensionTemplate.machine x) (2 * n + 8) (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate n true), List.replicate R false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate n true), ZeroPadding.pad R (CompareMachine.word (n + x.toNat)),
        List.replicate C false] := by
  have base := (SLoad.MaskFrame.step_of_clockReady (DimensionTemplate.ready x n)).pad ![Qa, R, C]
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · rfl
    · exact Desc.pad_nil R
    · exact Desc.pad_nil C
  · funext i
    fin_cases i
    · rfl
    · show ZeroPadding.pad R (UnaryTemplate.tape (n + x.toNat)) = _
      rw [ExtDecompositionBatch.pad_template R (n + x.toNat) hR]
      rfl
    · show ZeroPadding.pad C (List.replicate (n + 3) false) = _
      rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left hC]
      rfl

theorem one_local (S C : Nat) (hC : 1 ≤ C) :
    Step (HierarchyFixedWord.machine [true]) (2 * 1 + 2) (fun _ => 0)
      ![List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad S (List.replicate 1 true), List.replicate C false] := by
  have base := (Step.of_ready (HierarchyFixedWord.word_ready [true])).pad ![S, C]
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · exact Desc.pad_nil S
    · exact Desc.pad_nil C
  · funext i
    fin_cases i
    · rfl
    · show ZeroPadding.pad C (List.replicate 1 false) = _
      rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left hC]
      rfl

/-- Docked sum `![a, b, dst, log]`. -/
def sumM {U : Nat} (a b d l : Fin U) := RecoveryFocus.machine (![a, b, d, l] : Fin 4 → Fin U) ClockUnarySum.machine
/-- Docked product `![a, b, dst, log]` (`b` holds `word e`). -/
def mulM {U : Nat} (a b d l : Fin U) :=
  RecoveryFocus.machine (![a, b, d, l] : Fin 4 → Fin U) ClockUnaryProduct.machine
/-- Docked unary→word `![a, dst, log]` (`+ x.toNat`). -/
def wordM {U : Nat} (x : Bool) (a d l : Fin U) :=
  RecoveryFocus.machine (![a, d, l] : Fin 3 → Fin U) (DimensionTemplate.machine x)
/-- Docked constant `1` `![dst, log]`. -/
def oneM {U : Nat} (d l : Fin U) := RecoveryFocus.machine (![d, l] : Fin 2 → Fin U) (HierarchyFixedWord.machine [true])

theorem sum_step {U : Nat} (a b d l : Fin U) (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ l) (h4 : b ≠ d)
    (h5 : b ≠ l) (h6 : d ≠ l) (r s Qa Qb S C : Nat) (hC : r + s + 2 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ x, x = a ∨ x = b ∨ x = d ∨ x = l → H x = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate r true)) (hb : A b = ZeroPadding.pad Qb (List.replicate s true))
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (sumM a b d l) (2 * (r + s) + 6) H A H
      (Function.update A d (ZeroPadding.pad S (List.replicate (r + s) true))) :=
  SLoad.step_update (sum_local r s Qa Qb S C hC) 2
    (by
      intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd rfl hi
      · rfl)
    _ (SLoad.MaskFrame.quad_injective a b d l h1 h2 h3 h4 h5 h6) H A
    (by
      intro i
      fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH _ (Or.inr (Or.inr (Or.inr rfl))))
    (by
      intro i
      fin_cases i
      · exact ha
      · exact hb
      · exact hd
      · exact hl)

theorem mul_step {U : Nat} (a b d l : Fin U) (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ l) (h4 : b ≠ d)
    (h5 : b ≠ l) (h6 : d ≠ l) (x e Qa Qb S C : Nat) (hC : x * (2 * e + 3) + 2 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ y, y = a ∨ y = b ∨ y = d ∨ y = l → H y = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate x true)) (hb : A b = ZeroPadding.pad Qb (CompareMachine.word e))
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (mulM a b d l) (2 * (x * (2 * e + 3) + 2) + 2) H A H
      (Function.update A d (ZeroPadding.pad S (List.replicate (x * e) true))) :=
  SLoad.step_update (mul_local x e Qa Qb S C hC) 2
    (by
      intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd rfl hi
      · rfl)
    _ (SLoad.MaskFrame.quad_injective a b d l h1 h2 h3 h4 h5 h6) H A
    (by
      intro i
      fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH _ (Or.inr (Or.inr (Or.inr rfl))))
    (by
      intro i
      fin_cases i
      · exact ha
      · exact hb
      · exact hd
      · exact hl)

theorem word_step {U : Nat} (x : Bool) (a d l : Fin U) (h1 : a ≠ d) (h2 : a ≠ l) (h3 : d ≠ l)
    (n Qa R C : Nat) (hR : n + x.toNat + 2 ≤ R) (hC : n + 3 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ y, y = a ∨ y = d ∨ y = l → H y = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate n true))
    (hd : A d = List.replicate R false) (hl : A l = List.replicate C false) :
    Step (wordM x a d l) (2 * n + 8) H A H
      (Function.update A d (ZeroPadding.pad R (CompareMachine.word (n + x.toNat)))) :=
  SLoad.step_update (word_local x n Qa R C hR hC) 1
    (by
      intro i hi
      fin_cases i
      · rfl
      · exact absurd rfl hi
      · rfl)
    _ (SLoad.triple_injective a d l h1 h2 h3) H A
    (by
      intro i
      fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr rfl)))
    (by
      intro i
      fin_cases i
      · exact ha
      · exact hd
      · exact hl)

theorem one_step {U : Nat} (d l : Fin U) (h1 : d ≠ l) (S C : Nat) (hC : 1 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hHd : H d = 0) (hHl : H l = 0)
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (oneM d l) (2 * 1 + 2) H A H (Function.update A d (ZeroPadding.pad S (List.replicate 1 true))) :=
  SLoad.step_update (one_local S C hC) 0
    (by
      intro i hi
      fin_cases i
      · exact absurd rfl hi
      · rfl)
    _ (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij h1 | exact absurd hij.symm h1) H A
    (by
      intro i
      fin_cases i
      · exact hHd
      · exact hHl)
    (by
      intro i
      fin_cases i
      · exact hd
      · exact hl)

/-- A flag `[b]` read as the unary number `b.toNat`. -/
theorem flag_unary (Q : Nat) (b : Bool) :
    ZeroPadding.pad Q [b] = ZeroPadding.pad (max Q 1) (List.replicate b.toNat true) := by
  cases b
  · simp only [ZeroPadding.pad, Bool.toNat_false, List.replicate_zero, List.nil_append, List.length_nil,
      List.length_singleton, Nat.sub_zero]
    rw [show max Q 1 = (Q - 1) + 1 by omega, List.replicate_succ]
    rfl
  · simp only [ZeroPadding.pad, Bool.toNat_true, List.replicate_one, List.length_singleton]
    congr 2
    omega

theorem word0_step {U : Nat} (a d l : Fin U) (h1 : a ≠ d) (h2 : a ≠ l) (h3 : d ≠ l)
    (n Qa R C : Nat) (hR : n + 2 ≤ R) (hC : n + 3 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ y, y = a ∨ y = d ∨ y = l → H y = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate n true))
    (hd : A d = List.replicate R false) (hl : A l = List.replicate C false) :
    Step (wordM false a d l) (2 * n + 8) H A H
      (Function.update A d (ZeroPadding.pad R (CompareMachine.word n))) :=
  word_step false a d l h1 h2 h3 n Qa R C hR hC H A hH ha hd hl

/-! ## The moment phase: `N = JL·JL` -/

def momentM := Composition.machine (wordM false (0 : Fin 23) 6 5)
  (Composition.machine (mulM (0 : Fin 23) 6 7 5) (wordM false (7 : Fin 23) 4 5))

def momentCost (J : Nat) : Nat := 2 * J + 8 + 1 + (2 * (J * (2 * J + 3) + 2) + 2 + 1 + (2 * (J * J) + 8))

theorem moment_run (J Q R S C : Nat) (E : Fin 23 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Q (List.replicate J true)) (h4 : E 4 = List.replicate R false)
    (h5 : E 5 = List.replicate C false) (hscr : ∀ j : Fin 23, 6 ≤ j.val → E j = List.replicate S false)
    (hS : J + 2 ≤ S) (hC1 : J + 3 ≤ C) (hC2 : J * (2 * J + 3) + 2 ≤ C) (hC3 : J * J + 3 ≤ C)
    (hR : J * J + 2 ≤ R) :
    ∃ E' : Fin 23 → List Bool, Step momentM (momentCost J) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 4 = ZeroPadding.pad R (CompareMachine.word (J * J)) ∧
      (∀ j : Fin 23, j.val < 4 → E' j = E j) ∧ E' 5 = E 5 := by
  set E1 := Function.update E 6 (ZeroPadding.pad S (CompareMachine.word J)) with hE1
  set E2 := Function.update E1 7 (ZeroPadding.pad S (List.replicate (J * J) true)) with hE2
  have s1 := word0_step (0 : Fin 23) 6 5 (by decide) (by decide) (by decide) J Q S C hS hC1 (fun _ => 0) E
    (fun _ _ => rfl) h0 (hscr 6 (by decide)) h5
  have s2 := mul_step (0 : Fin 23) 6 7 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) J J Q S S C hC2 (fun _ => 0) E1 (fun _ _ => rfl) (by simp [E1, h0]) (by simp [E1])
    (by simp [E1, hscr 7 (by decide)]) (by simp [E1, h5])
  have s3 := word0_step (7 : Fin 23) 4 5 (by decide) (by decide) (by decide) (J * J) S R C hR hC3 (fun _ => 0)
    E2 (fun _ _ => rfl) (by simp [E2]) (by simp [E1, E2, h4]) (by simp [E1, E2, h5])
  have hall : Step momentM _ _ _ _ _ := s1.seq (s2.seq s3)
  refine ⟨_, hall, by simp, ?_, by simp [E1, E2]⟩
  intro j hj
  have hne : ∀ c : Fin 23, 4 ≤ c.val → j ≠ c := fun c hc e => by rw [e] at hj; omega
  simp [E1, E2, hne 4 (by decide), hne 6 (by decide), hne 7 (by decide)]

/-! ## The clause phase: `N = a + (b + a·b)`, `a = JL + [nL]`, `b = JR + [nR]` -/

def clauseM := Composition.machine (sumM (0 : Fin 23) 2 6 5) (Composition.machine (sumM (1 : Fin 23) 3 7 5)
  (Composition.machine (wordM false (7 : Fin 23) 8 5) (Composition.machine (mulM (6 : Fin 23) 8 9 5)
  (Composition.machine (sumM (7 : Fin 23) 9 10 5) (Composition.machine (sumM (6 : Fin 23) 10 11 5)
  (wordM false (11 : Fin 23) 4 5))))))

def clauseCost (a b : Nat) : Nat :=
  2 * a + 6 + 1 + (2 * b + 6 + 1 + (2 * b + 8 + 1 + (2 * (a * (2 * b + 3) + 2) + 2 + 1 +
    (2 * (b + a * b) + 6 + 1 + (2 * (a + (b + a * b)) + 6 + 1 + (2 * (a + (b + a * b)) + 8))))))

theorem clause_run (JL JR : Nat) (nL nR : Bool) (Q Qf R S C : Nat) (E : Fin 23 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Q (List.replicate JL true)) (h1 : E 1 = ZeroPadding.pad Q (List.replicate JR true))
    (h2 : E 2 = ZeroPadding.pad Qf [nL]) (h3 : E 3 = ZeroPadding.pad Qf [nR])
    (h4 : E 4 = List.replicate R false) (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 23, 6 ≤ j.val → E j = List.replicate S false)
    (hS : JR + nR.toNat + 2 ≤ S)
    (hCa : JL + nL.toNat + 2 ≤ C) (hCb : JR + nR.toNat + 3 ≤ C)
    (hCm : (JL + nL.toNat) * (2 * (JR + nR.toNat) + 3) + 2 ≤ C)
    (hCs : (JR + nR.toNat) + (JL + nL.toNat) * (JR + nR.toNat) + 2 ≤ C)
    (hCt : (JL + nL.toNat) + ((JR + nR.toNat) + (JL + nL.toNat) * (JR + nR.toNat)) + 3 ≤ C)
    (hR : (JL + nL.toNat) + ((JR + nR.toNat) + (JL + nL.toNat) * (JR + nR.toNat)) + 2 ≤ R) :
    ∃ E' : Fin 23 → List Bool, Step clauseM (clauseCost (JL + nL.toNat) (JR + nR.toNat)) (fun _ => 0) E
      (fun _ => 0) E' ∧
      E' 4 = ZeroPadding.pad R (CompareMachine.word
        ((JL + nL.toNat) + ((JR + nR.toNat) + (JL + nL.toNat) * (JR + nR.toNat)))) ∧
      (∀ j : Fin 23, j.val < 4 → E' j = E j) ∧ E' 5 = E 5 := by
  set a := JL + nL.toNat with ha
  set b := JR + nR.toNat with hb
  have h2' : E 2 = ZeroPadding.pad (max Qf 1) (List.replicate nL.toNat true) := by rw [h2, flag_unary]
  have h3' : E 3 = ZeroPadding.pad (max Qf 1) (List.replicate nR.toNat true) := by rw [h3, flag_unary]
  set E1 := Function.update E 6 (ZeroPadding.pad S (List.replicate a true)) with hE1
  set E2 := Function.update E1 7 (ZeroPadding.pad S (List.replicate b true)) with hE2
  set E3 := Function.update E2 8 (ZeroPadding.pad S (CompareMachine.word b)) with hE3
  set E4 := Function.update E3 9 (ZeroPadding.pad S (List.replicate (a * b) true)) with hE4
  set E5 := Function.update E4 10 (ZeroPadding.pad S (List.replicate (b + a * b) true)) with hE5
  set E6 := Function.update E5 11 (ZeroPadding.pad S (List.replicate (a + (b + a * b)) true)) with hE6
  have s1 := sum_step (0 : Fin 23) 2 6 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    JL nL.toNat Q (max Qf 1) S C hCa (fun _ => 0) E (fun _ _ => rfl) h0 h2' (hscr 6 (by decide)) h5
  have s2 := sum_step (1 : Fin 23) 3 7 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    JR nR.toNat Q (max Qf 1) S C (by omega) (fun _ => 0) E1 (fun _ _ => rfl) (by simp [E1, h1])
    (by simp [E1, h3']) (by simp [E1, hscr 7 (by decide)]) (by simp [E1, h5])
  have s3 := word0_step (7 : Fin 23) 8 5 (by decide) (by decide) (by decide) b S S C hS hCb (fun _ => 0) E2
    (fun _ _ => rfl) (by simp [E2]) (by simp [E1, E2, hscr 8 (by decide)]) (by simp [E1, E2, h5])
  have s4 := mul_step (6 : Fin 23) 8 9 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a b S S S C hCm (fun _ => 0) E3 (fun _ _ => rfl) (by simp [E1, E2, E3])
    (by simp [E3]) (by simp [E1, E2, E3, hscr 9 (by decide)]) (by simp [E1, E2, E3, h5])
  have s5 := sum_step (7 : Fin 23) 9 10 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) b (a * b) S S S C hCs (fun _ => 0) E4 (fun _ _ => rfl) (by simp [E2, E3, E4])
    (by simp [E4]) (by simp [E1, E2, E3, E4, hscr 10 (by decide)]) (by simp [E1, E2, E3, E4, h5])
  have s6 := sum_step (6 : Fin 23) 10 11 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a (b + a * b) S S S C (by omega) (fun _ => 0) E5 (fun _ _ => rfl)
    (by simp [E1, E2, E3, E4, E5]) (by simp [E5]) (by simp [E1, E2, E3, E4, E5, hscr 11 (by decide)])
    (by simp [E1, E2, E3, E4, E5, h5])
  have s7 := word0_step (11 : Fin 23) 4 5 (by decide) (by decide) (by decide) (a + (b + a * b)) S R C hR hCt
    (fun _ => 0) E6 (fun _ _ => rfl) (by simp [E6]) (by simp [E1, E2, E3, E4, E5, E6, h4])
    (by simp [E1, E2, E3, E4, E5, E6, h5])
  have hall : Step clauseM _ _ _ _ _ := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))
  refine ⟨_, hall, by simp, ?_, by simp [E1, E2, E3, E4, E5, E6]⟩
  intro j hj
  have hne : ∀ c : Fin 23, 4 ≤ c.val → j ≠ c := fun c hc e => by rw [e] at hj; omega
  simp [E1, E2, E3, E4, E5, E6, hne 4 (by decide), hne 6 (by decide), hne 7 (by decide), hne 8 (by decide),
    hne 9 (by decide), hne 10 (by decide), hne 11 (by decide)]

/-! ## The penalty phase: one side, `penLen s J`, switched on the auxiliary flag

Side universe `Fin 10`: `0` `1^J` · `1` aux flag `[!s]` · `2` `word J` · `3` `J²` · `4` `word J²` (aux) / `1` (sys) ·
`5` `J³` · `6` `J²·J²` · `7` partial sum · `8` result · `9` log. -/

/-- Systematic side: `1 + (J + J·J)`. -/
def sideSys := Composition.machine (wordM false (0 : Fin 10) 2 9) (Composition.machine (mulM (0 : Fin 10) 2 3 9)
  (Composition.machine (sumM (0 : Fin 10) 3 7 9) (Composition.machine (oneM (4 : Fin 10) 9) (sumM (4 : Fin 10) 7 8 9))))

/-- Auxiliary side: `J·J + (J·J·J + J·J·(J·J))`. -/
def sideAux := Composition.machine (wordM false (0 : Fin 10) 2 9) (Composition.machine (mulM (0 : Fin 10) 2 3 9)
  (Composition.machine (mulM (3 : Fin 10) 2 5 9) (Composition.machine (wordM false (3 : Fin 10) 4 9)
  (Composition.machine (mulM (3 : Fin 10) 4 6 9) (Composition.machine (sumM (5 : Fin 10) 6 7 9)
  (sumM (3 : Fin 10) 7 8 9))))))

/-- One side: aux flag set → auxiliary polynomial, else systematic. -/
def side := CloseoutRowsOriginalSwitch.machine sideAux sideSys (1 : Fin 10)

def sysCost (J : Nat) : Nat :=
  2 * J + 8 + 1 + (2 * (J * (2 * J + 3) + 2) + 2 + 1 + (2 * (J + J * J) + 6 + 1 +
    (2 * 1 + 2 + 1 + (2 * (1 + (J + J * J)) + 6))))

def auxCost (J : Nat) : Nat :=
  2 * J + 8 + 1 + (2 * (J * (2 * J + 3) + 2) + 2 + 1 + (2 * (J * J * (2 * J + 3) + 2) + 2 + 1 +
    (2 * (J * J) + 8 + 1 + (2 * (J * J * (2 * (J * J) + 3) + 2) + 2 + 1 +
    (2 * (J * J * J + J * J * (J * J)) + 6 + 1 + (2 * (J * J + (J * J * J + J * J * (J * J))) + 6))))))

def sideCost (aux : Bool) (J : Nat) : Nat := if aux then auxCost J + 2 else sysCost J + 2

/-- The side's size conditions (both branches). -/
structure SideFits (J S C : Nat) : Prop where
  s1 : J + 2 ≤ S
  s2 : J * J + 2 ≤ S
  c1 : J + 3 ≤ C
  c2 : J * (2 * J + 3) + 2 ≤ C
  c3 : J + J * J + 2 ≤ C
  c4 : 1 ≤ C
  c5 : 1 + (J + J * J) + 2 ≤ C
  c6 : J * J * (2 * J + 3) + 2 ≤ C
  c7 : J * J + 3 ≤ C
  c8 : J * J * (2 * (J * J) + 3) + 2 ≤ C
  c9 : J * J * J + J * J * (J * J) + 2 ≤ C
  c10 : J * J + (J * J * J + J * J * (J * J)) + 2 ≤ C

theorem read_flag (Q : Nat) (b : Bool) : readTapeBit (ZeroPadding.pad Q [b]) 0 = b := by
  simp [ZeroPadding.pad, readTapeBit]

theorem side_run (aux : Bool) (J Q Qf S C : Nat) (E : Fin 10 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Q (List.replicate J true)) (h1 : E 1 = ZeroPadding.pad Qf [aux])
    (hscr : ∀ j : Fin 10, 2 ≤ j.val → j.val < 9 → E j = List.replicate S false)
    (h9 : E 9 = List.replicate C false) (hf : SideFits J S C) :
    ∃ E' : Fin 10 → List Bool, Step side (sideCost aux J) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 8 = ZeroPadding.pad S (List.replicate (SourceRequest.MonomialSpec.penLen (!aux) J) true) ∧
      E' 0 = E 0 ∧ E' 1 = E 1 ∧ E' 9 = E 9 := by
  have hw := word0_step (0 : Fin 10) 2 9 (by decide) (by decide) (by decide) J Q S C hf.s1 hf.c1 (fun _ => 0) E
    (fun _ _ => rfl) h0 (hscr 2 (by decide) (by decide)) h9
  set E1 := Function.update E 2 (ZeroPadding.pad S (CompareMachine.word J)) with hE1
  have hm := mul_step (0 : Fin 10) 2 3 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) J J Q S S C hf.c2 (fun _ => 0) E1 (fun _ _ => rfl) (by simp [E1, h0]) (by simp [E1])
    (by simp [E1, hscr 3 (by decide) (by decide)]) (by simp [E1, h9])
  set E2 := Function.update E1 3 (ZeroPadding.pad S (List.replicate (J * J) true)) with hE2
  cases aux with
  | false =>
    have s3 := sum_step (0 : Fin 10) 3 7 9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) J (J * J) Q S S C hf.c3 (fun _ => 0) E2 (fun _ _ => rfl) (by simp [E1, E2, h0])
      (by simp [E2]) (by simp [E1, E2, hscr 7 (by decide) (by decide)]) (by simp [E1, E2, h9])
    set E3 := Function.update E2 7 (ZeroPadding.pad S (List.replicate (J + J * J) true)) with hE3
    have s4 := one_step (4 : Fin 10) 9 (by decide) S C hf.c4 (fun _ => 0) E3 rfl rfl
      (by simp [E1, E2, E3, hscr 4 (by decide) (by decide)]) (by simp [E1, E2, E3, h9])
    set E4 := Function.update E3 4 (ZeroPadding.pad S (List.replicate 1 true)) with hE4
    have s5 := sum_step (4 : Fin 10) 7 8 9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) 1 (J + J * J) S S S C hf.c5 (fun _ => 0) E4 (fun _ _ => rfl) (by simp [E4])
      (by simp [E3, E4]) (by simp [E1, E2, E3, E4, hscr 8 (by decide) (by decide)])
      (by simp [E1, E2, E3, E4, h9])
    have hall : Step sideSys _ _ _ _ _ := hw.seq (hm.seq (s3.seq (s4.seq s5)))
    have hs : Step side (sysCost J + 2) (fun _ => 0) E (fun _ => 0) _ :=
      CloseoutRowsOriginalSwitch.false_run _ _ _ hall (by rw [h1]; exact read_flag Qf false)
    refine ⟨_, hs, ?_, by simp [E1, E2, E3, E4], by simp [E1, E2, E3, E4], by simp [E1, E2, E3, E4]⟩
    simp [SourceRequest.MonomialSpec.penLen]
  | true =>
    have s3 := mul_step (3 : Fin 10) 2 5 9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (J * J) J S S S C hf.c6 (fun _ => 0) E2 (fun _ _ => rfl) (by simp [E2])
      (by simp [E1, E2]) (by simp [E1, E2, hscr 5 (by decide) (by decide)]) (by simp [E1, E2, h9])
    set E3 := Function.update E2 5 (ZeroPadding.pad S (List.replicate (J * J * J) true)) with hE3
    have s4 := word0_step (3 : Fin 10) 4 9 (by decide) (by decide) (by decide) (J * J) S S C hf.s2 hf.c7
      (fun _ => 0) E3 (fun _ _ => rfl) (by simp [E2, E3]) (by simp [E1, E2, E3, hscr 4 (by decide) (by decide)])
      (by simp [E1, E2, E3, h9])
    set E4 := Function.update E3 4 (ZeroPadding.pad S (CompareMachine.word (J * J))) with hE4
    have s5 := mul_step (3 : Fin 10) 4 6 9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (J * J) (J * J) S S S C hf.c8 (fun _ => 0) E4 (fun _ _ => rfl) (by simp [E2, E3, E4])
      (by simp [E4]) (by simp [E1, E2, E3, E4, hscr 6 (by decide) (by decide)]) (by simp [E1, E2, E3, E4, h9])
    set E5 := Function.update E4 6 (ZeroPadding.pad S (List.replicate (J * J * (J * J)) true)) with hE5
    have s6 := sum_step (5 : Fin 10) 6 7 9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (J * J * J) (J * J * (J * J)) S S S C hf.c9 (fun _ => 0) E5 (fun _ _ => rfl)
      (by simp [E3, E4, E5]) (by simp [E5]) (by simp [E1, E2, E3, E4, E5, hscr 7 (by decide) (by decide)])
      (by simp [E1, E2, E3, E4, E5, h9])
    set E6 := Function.update E5 7 (ZeroPadding.pad S (List.replicate (J * J * J + J * J * (J * J)) true))
      with hE6
    have s7 := sum_step (3 : Fin 10) 7 8 9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (J * J) (J * J * J + J * J * (J * J)) S S S C hf.c10 (fun _ => 0) E6 (fun _ _ => rfl)
      (by simp [E2, E3, E4, E5, E6]) (by simp [E6])
      (by simp [E1, E2, E3, E4, E5, E6, hscr 8 (by decide) (by decide)])
      (by simp [E1, E2, E3, E4, E5, E6, h9])
    have hall : Step sideAux _ _ _ _ _ := hw.seq (hm.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))
    have hs : Step side (auxCost J + 2) (fun _ => 0) E (fun _ => 0) _ :=
      CloseoutRowsOriginalSwitch.true_run _ _ _ hall (by rw [h1]; exact read_flag Qf true)
    refine ⟨_, hs, ?_, by simp [E1, E2, E3, E4, E5, E6], by simp [E1, E2, E3, E4, E5, E6],
      by simp [E1, E2, E3, E4, E5, E6]⟩
    simp [SourceRequest.MonomialSpec.penLen]

/-- The left side's ports in the stage universe. -/
def slL : Fin 10 → Fin 23 := ![0, 2, 6, 7, 8, 9, 10, 11, 12, 5]
/-- The right side's ports in the stage universe. -/
def slR : Fin 10 → Fin 23 := ![1, 3, 13, 14, 15, 16, 17, 18, 19, 5]

theorem slL_inj : Function.Injective slL := by decide
theorem slR_inj : Function.Injective slR := by decide

def penaltyM := Composition.machine (RecoveryFocus.machine slL side)
  (Composition.machine (RecoveryFocus.machine slR side)
  (Composition.machine (sumM (12 : Fin 23) 19 20 5) (wordM false (20 : Fin 23) 4 5)))

def penaltyCost (aL aR : Bool) (JL JR : Nat) : Nat :=
  sideCost aL JL + 1 + (sideCost aR JR + 1 +
    (2 * (SourceRequest.MonomialSpec.penLen (!aL) JL + SourceRequest.MonomialSpec.penLen (!aR) JR) + 6 + 1 +
    (2 * (SourceRequest.MonomialSpec.penLen (!aL) JL + SourceRequest.MonomialSpec.penLen (!aR) JR) + 8)))

theorem penalty_run (aL aR : Bool) (JL JR Q Qf R S C : Nat) (E : Fin 23 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Q (List.replicate JL true)) (h1 : E 1 = ZeroPadding.pad Q (List.replicate JR true))
    (h2 : E 2 = ZeroPadding.pad Qf [aL]) (h3 : E 3 = ZeroPadding.pad Qf [aR])
    (h4 : E 4 = List.replicate R false) (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 23, 6 ≤ j.val → E j = List.replicate S false)
    (hfL : SideFits JL S C) (hfR : SideFits JR S C)
    (hCs : SourceRequest.MonomialSpec.penLen (!aL) JL + SourceRequest.MonomialSpec.penLen (!aR) JR + 3 ≤ C)
    (hR : SourceRequest.MonomialSpec.penLen (!aL) JL + SourceRequest.MonomialSpec.penLen (!aR) JR + 2 ≤ R) :
    ∃ E' : Fin 23 → List Bool, Step penaltyM (penaltyCost aL aR JL JR) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 4 = ZeroPadding.pad R (CompareMachine.word
        (SourceRequest.MonomialSpec.penLen (!aL) JL + SourceRequest.MonomialSpec.penLen (!aR) JR)) ∧
      (∀ j : Fin 23, j.val < 4 → E' j = E j) ∧ E' 5 = E 5 := by
  set pL := SourceRequest.MonomialSpec.penLen (!aL) JL with hpL
  set pR := SourceRequest.MonomialSpec.penLen (!aR) JR with hpR
  obtain ⟨EL, sL, rL, kL0, kL1, kL9⟩ := side_run aL JL Q Qf S C (fun j => E (slL j)) h0 h2
    (by
      intro j hj hj'
      apply hscr
      fin_cases j <;> simp_all [slL])
    h5 hfL
  have dL := sL.dock slL slL_inj (fun _ => 0) E (fun _ => rfl) (fun _ => rfl)
  rw [dockH_existing slL (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at dL
  set A1 := install slL E EL with hA1
  have outL : ∀ x : Fin 23, (∀ i, slL i ≠ x) → A1 x = E x := fun x hx => install_other slL E EL x hx
  have a1_12 : A1 12 = ZeroPadding.pad S (List.replicate pL true) := by
    show install slL E EL (slL 8) = _
    rw [install_slot slL slL_inj]
    exact rL
  have a1_5 : A1 5 = E 5 := by
    show install slL E EL (slL 9) = _
    rw [install_slot slL slL_inj]
    exact kL9
  have a1_0 : A1 0 = E 0 := by
    show install slL E EL (slL 0) = _
    rw [install_slot slL slL_inj]
    exact kL0
  have a1_2 : A1 2 = E 2 := by
    show install slL E EL (slL 1) = _
    rw [install_slot slL slL_inj]
    exact kL1
  obtain ⟨ER, sR, rR, kR0, kR1, kR9⟩ := side_run aR JR Q Qf S C (fun j => A1 (slR j))
    (by
      show A1 1 = _
      rw [outL 1 (by intro i; fin_cases i <;> decide)]
      exact h1)
    (by
      show A1 3 = _
      rw [outL 3 (by intro i; fin_cases i <;> decide)]
      exact h3)
    (by
      intro j hj hj'
      show A1 (slR j) = _
      have hn : ∀ i, slL i ≠ slR j := by
        intro i
        fin_cases j <;> simp at hj hj' <;> fin_cases i <;> decide
      rw [outL _ hn]
      apply hscr
      fin_cases j <;> simp_all [slR])
    (by
      show A1 5 = _
      rw [a1_5, h5])
    hfR
  have dR := sR.dock slR slR_inj (fun _ => 0) A1 (fun _ => rfl) (fun _ => rfl)
  rw [dockH_existing slR (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at dR
  set A2 := install slR A1 ER with hA2
  have outR : ∀ x : Fin 23, (∀ i, slR i ≠ x) → A2 x = A1 x := fun x hx => install_other slR A1 ER x hx
  have a2_19 : A2 19 = ZeroPadding.pad S (List.replicate pR true) := by
    show install slR A1 ER (slR 8) = _
    rw [install_slot slR slR_inj]
    exact rR
  have a2_12 : A2 12 = ZeroPadding.pad S (List.replicate pL true) := by
    rw [outR 12 (by intro i; fin_cases i <;> decide)]
    exact a1_12
  have a2_5 : A2 5 = E 5 := by
    show install slR A1 ER (slR 9) = _
    rw [install_slot slR slR_inj, kR9]
    exact a1_5
  have a2_20 : A2 20 = List.replicate S false := by
    rw [outR 20 (by intro i; fin_cases i <;> decide), outL 20 (by intro i; fin_cases i <;> decide)]
    exact hscr 20 (by decide)
  have a2_4 : A2 4 = List.replicate R false := by
    rw [outR 4 (by intro i; fin_cases i <;> decide), outL 4 (by intro i; fin_cases i <;> decide)]
    exact h4
  have s3 := sum_step (12 : Fin 23) 19 20 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) pL pR S S S C (by omega) (fun _ => 0) A2 (fun _ _ => rfl) a2_12 a2_19 a2_20
    (by rw [a2_5, h5])
  set A3 := Function.update A2 20 (ZeroPadding.pad S (List.replicate (pL + pR) true)) with hA3
  have s4 := word0_step (20 : Fin 23) 4 5 (by decide) (by decide) (by decide) (pL + pR) S R C hR hCs
    (fun _ => 0) A3 (fun _ _ => rfl) (by simp [A3]) (by simp [A3, a2_4]) (by simp [A3, a2_5, h5])
  have hall : Step penaltyM _ _ _ _ _ := dL.seq (dR.seq (s3.seq s4))
  refine ⟨_, hall, by simp, ?_, by simp [A3, a2_5]⟩
  intro j hj
  have hne : ∀ c : Fin 23, 4 ≤ c.val → j ≠ c := fun c hc e => by rw [e] at hj; omega
  simp only [A3, Function.update_of_ne (hne 4 (by decide)), Function.update_of_ne (hne 20 (by decide))]
  fin_cases j
  · show A2 0 = E 0
    rw [outR 0 (by intro i; fin_cases i <;> decide)]
    exact a1_0
  · show install slR A1 ER (slR 0) = _
    rw [install_slot slR slR_inj, kR0]
    show A1 1 = E 1
    exact outL 1 (by intro i; fin_cases i <;> decide)
  · show A2 2 = E 2
    rw [outR 2 (by intro i; fin_cases i <;> decide)]
    exact a1_2
  · show install slR A1 ER (slR 1) = _
    rw [install_slot slR slR_inj, kR1]
    show A1 3 = E 3
    exact outL 3 (by intro i; fin_cases i <;> decide)
  · exact absurd hj (by decide)
  all_goals exact absurd hj (by decide)

/-! ## The per-phase stage at `siteLen` -/

/-- The size bound: `8·M⁴`, `M = JL + JR + 2` (every intermediate value and log fits under it). -/
def big (JL JR : Nat) : Nat := 8 * ((JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2)))

theorem pow_facts (J M : Nat) (hJ : J ≤ M) (hM : 2 ≤ M) :
    J ≤ M * M * (M * M) ∧ J * J ≤ M * M * (M * M) ∧ J * J * J ≤ M * M * (M * M) ∧
      J * J * (J * J) ≤ M * M * (M * M) ∧ 16 ≤ M * M * (M * M) := by
  have h1 : M ≤ M * M := Nat.le_mul_of_pos_left M (by omega)
  have h2 : M * M ≤ M * M * (M * M) := Nat.le_mul_of_pos_right (M * M) (by positivity)
  have h3 : M * M * M ≤ M * M * (M * M) := Nat.mul_le_mul_left (M * M) h1
  have jj : J * J ≤ M * M := Nat.mul_le_mul hJ hJ
  have jjj : J * J * J ≤ M * M * M := Nat.mul_le_mul jj hJ
  have j4 : J * J * (J * J) ≤ M * M * (M * M) := Nat.mul_le_mul jj jj
  have m4 : 2 * 2 * (2 * 2) ≤ M * M * (M * M) := Nat.mul_le_mul (Nat.mul_le_mul hM hM) (Nat.mul_le_mul hM hM)
  exact ⟨by omega, by omega, by omega, j4, by omega⟩

theorem sideFits_of (J M S C : Nat) (hJ : J ≤ M) (hM : 2 ≤ M) (hS : 8 * (M * M * (M * M)) ≤ S)
    (hC : 8 * (M * M * (M * M)) ≤ C) : SideFits J S C := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := pow_facts J M hJ hM
  refine ⟨by omega, by omega, by omega, ?_, by omega, by omega, by omega, ?_, by omega, ?_, by omega, by omega⟩
  · have e : J * (2 * J + 3) = 2 * (J * J) + 3 * J := by ring
    omega
  · have e : J * J * (2 * J + 3) = 2 * (J * J * J) + 3 * (J * J) := by ring
    omega
  · have e : J * J * (2 * (J * J) + 3) = 2 * (J * J * (J * J)) + 3 * (J * J) := by ring
    omega

theorem penLen_le (s : Bool) (J M : Nat) (hJ : J ≤ M) (hM : 2 ≤ M) :
    SourceRequest.MonomialSpec.penLen s J ≤ 3 * (M * M * (M * M)) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := pow_facts J M hJ hM
  cases s
  · simp only [SourceRequest.MonomialSpec.penLen, Bool.false_eq_true, if_false]
    omega
  · simp only [SourceRequest.MonomialSpec.penLen, if_true]
    omega

theorem litLen_eq (n : Bool) (J : Nat) : SourceRequest.MonomialSpec.litLen n J = J + n.toNat := by
  cases n
  · simp [SourceRequest.MonomialSpec.litLen]
  · simp only [SourceRequest.MonomialSpec.litLen, if_true, Bool.toNat_true]
    omega

/-- The flag each phase reads: penalty the AUXILIARY flag `!s` (the literal guard's `decide (systematicBits ≤ index)`),
clause the sign `n`, moment none. -/
def flagOf : Phase → Bool → Bool → Bool
  | .penalty, s, _ => !s
  | .moment, _, _ => false
  | .clause, _, n => n

/-- **One fixed machine per phase.** -/
def machine : Phase → (Σ s, Machine 23 s)
  | .penalty => ⟨_, penaltyM⟩
  | .moment => ⟨_, momentM⟩
  | .clause => ⟨_, clauseM⟩

def cost : Phase → Bool → Bool → Bool → Bool → Nat → Nat → Nat
  | .penalty, sL, sR, _, _, JL, JR => penaltyCost (!sL) (!sR) JL JR
  | .moment, _, _, _, _, JL, _ => momentCost JL
  | .clause, _, _, nL, nR, JL, JR => clauseCost (JL + nL.toNat) (JR + nR.toNat)

theorem count_run (ph : Phase) (sL sR nL nR : Bool) (JL JR Q Qf R S C : Nat) (E : Fin 23 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Q (List.replicate JL true)) (h1 : E 1 = ZeroPadding.pad Q (List.replicate JR true))
    (h2 : E 2 = ZeroPadding.pad Qf [flagOf ph sL nL]) (h3 : E 3 = ZeroPadding.pad Qf [flagOf ph sR nR])
    (h4 : E 4 = List.replicate R false) (h5 : E 5 = List.replicate C false)
    (hscr : ∀ j : Fin 23, 6 ≤ j.val → E j = List.replicate S false)
    (hS : big JL JR ≤ S) (hC : big JL JR ≤ C) (hR : big JL JR ≤ R) :
    ∃ E' : Fin 23 → List Bool,
      Step (machine ph).2 (cost ph sL sR nL nR JL JR) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 4 = ZeroPadding.pad R (CompareMachine.word (SourceRequest.MonomialSpec.siteLen ph sL sR nL nR JL JR)) ∧
      (∀ j : Fin 23, j.val < 4 → E' j = E j) ∧ E' 5 = E 5 := by
  set M := JL + JR + 2 with hM
  have hM2 : 2 ≤ M := by omega
  obtain ⟨_, _, _, _, P16⟩ := pow_facts JL M (by omega) hM2
  unfold big at hS hC hR
  rw [← hM] at hS hC hR
  cases ph with
  | penalty =>
    have hpL := penLen_le (!(!sL)) JL M (by omega) hM2
    have hpR := penLen_le (!(!sR)) JR M (by omega) hM2
    obtain ⟨E', hs, hout, hk, h5'⟩ := penalty_run (!sL) (!sR) JL JR Q Qf R S C E h0 h1 h2 h3 h4 h5 hscr
      (sideFits_of JL M S C (by omega) hM2 hS hC) (sideFits_of JR M S C (by omega) hM2 hS hC)
      (by omega) (by omega)
    refine ⟨E', hs, ?_, hk, h5'⟩
    rw [hout]
    simp [SourceRequest.MonomialSpec.siteLen]
  | moment =>
    obtain ⟨f1, f2, _, _, _⟩ := pow_facts JL M (by omega) hM2
    have e : JL * (2 * JL + 3) = 2 * (JL * JL) + 3 * JL := by ring
    obtain ⟨E', hs, hout, hk, h5'⟩ := moment_run JL Q R S C E h0 h4 h5 hscr (by omega) (by omega)
      (by omega) (by omega) (by omega)
    exact ⟨E', hs, hout, hk, h5'⟩
  | clause =>
    have ha : JL + nL.toNat ≤ M := by cases nL <;> simp <;> omega
    have hb : JR + nR.toNat ≤ M := by cases nR <;> simp <;> omega
    have hab : (JL + nL.toNat) * (JR + nR.toNat) ≤ M * M := Nat.mul_le_mul ha hb
    have hMM : M * M ≤ M * M * (M * M) := Nat.le_mul_of_pos_right (M * M) (by positivity)
    have hMle : M ≤ M * M := Nat.le_mul_of_pos_left M (by omega)
    have e : (JL + nL.toNat) * (2 * (JR + nR.toNat) + 3) =
        2 * ((JL + nL.toNat) * (JR + nR.toNat)) + 3 * (JL + nL.toNat) := by ring
    obtain ⟨E', hs, hout, hk, h5'⟩ := clause_run JL JR nL nR Q Qf R S C E h0 h1 h2 h3 h4 h5 hscr
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨E', hs, ?_, hk, h5'⟩
    rw [hout]
    simp only [SourceRequest.MonomialSpec.siteLen, litLen_eq]

/-- **`word N` on `nT`, docked** by an injective `sl : Fin 23 → Fin U` (`sl 0`/`sl 1` the reader's `1^JL`/`1^JR`, `sl 2`/`sl 3`
the flags, `sl 4` = `nT`, `sl 5` log, `sl 6..22` scratch): ONE machine per phase; `nT` ends as
`pad R (CompareMachine.word (siteLen …))`, `sl 0..3` and the log are kept, off-dock tapes and every head unchanged. -/
theorem count_step {U : Nat} (sl : Fin 23 → Fin U) (hsl : Function.Injective sl)
    (ph : Phase) (sL sR nL nR : Bool) (JL JR Q Qf R S C : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Q (List.replicate JL true))
    (h1 : A (sl 1) = ZeroPadding.pad Q (List.replicate JR true))
    (h2 : A (sl 2) = ZeroPadding.pad Qf [flagOf ph sL nL]) (h3 : A (sl 3) = ZeroPadding.pad Qf [flagOf ph sR nR])
    (h4 : A (sl 4) = List.replicate R false) (h5 : A (sl 5) = List.replicate C false)
    (hscr : ∀ j : Fin 23, 6 ≤ j.val → A (sl j) = List.replicate S false)
    (hS : big JL JR ≤ S) (hC : big JL JR ≤ C) (hR : big JL JR ≤ R) :
    ∃ A' : Fin U → List Bool,
      Step (RecoveryFocus.machine sl (machine ph).2) (cost ph sL sR nL nR JL JR) H A H A' ∧
      A' (sl 4) = ZeroPadding.pad R (CompareMachine.word (SourceRequest.MonomialSpec.siteLen ph sL sR nL nR JL JR)) ∧
      (∀ j : Fin 23, j.val < 4 → A' (sl j) = A (sl j)) ∧ A' (sl 5) = A (sl 5) ∧
      (∀ x, (∀ j, sl j ≠ x) → A' x = A x) := by
  obtain ⟨E', hs, hout, hk, h5'⟩ := count_run ph sL sR nL nR JL JR Q Qf R S C (fun j => A (sl j))
    h0 h1 h2 h3 h4 h5 hscr hS hC hR
  have d := hs.dock sl hsl H A (fun j => hH j) (fun j => rfl)
  rw [dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_, ?_, ?_⟩
  · rw [install_slot sl hsl]; exact hout
  · intro j hj; rw [install_slot sl hsl]; exact hk j hj
  · rw [install_slot sl hsl]; exact h5'
  · intro x hx; exact install_other sl A E' x hx

/-! ## At the consumer's quantity -/

section consumer
open NearCubicWires.SourceInterfaces NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairSource.CloseoutFinal
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

theorem nT_step {U : Nat} (sl : Fin 23 → Fin U) (hsl : Function.Injective sl)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (Q Qf R S C : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Q (List.replicate
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length true))
    (h1 : A (sl 1) = ZeroPadding.pad Q (List.replicate
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length true))
    (h2 : A (sl 2) = ZeroPadding.pad Qf [flagOf ph
      (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left)])
    (h3 : A (sl 3) = ZeroPadding.pad Qf [flagOf ph
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).right)])
    (h4 : A (sl 4) = List.replicate R false) (h5 : A (sl 5) = List.replicate C false)
    (hscr : ∀ j : Fin 23, 6 ≤ j.val → A (sl j) = List.replicate S false)
    (hS : big (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length ≤ S)
    (hC : big (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length ≤ C)
    (hR : big (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length ≤ R) :
    ∃ A' : Fin U → List Bool,
      Step (RecoveryFocus.machine sl (machine ph).2)
        (cost ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
          (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
          (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
          (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
          (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length) H A H A' ∧
      A' (sl 4) = ZeroPadding.pad R (CompareMachine.word (SourceRequest.FactorLoop.monomials coordinate ph ci).length) ∧
      (∀ j : Fin 23, j.val < 4 → A' (sl j) = A (sl j)) ∧ A' (sl 5) = A (sl 5) ∧
      (∀ x, (∀ j, sl j ≠ x) → A' x = A x) := by
  obtain ⟨A', hs, hout, hk, h5', hoff⟩ := count_step sl hsl ph _ _ _ _ _ _ Q Qf R S C H A hH h0 h1 h2 h3 h4 h5
    hscr hS hC hR
  refine ⟨A', hs, ?_, hk, h5', hoff⟩
  rw [hout, SourceRequest.MonomialSpec.monomials_len]

end consumer


end
end NearCubicWires.SourceFactorSel.Count
