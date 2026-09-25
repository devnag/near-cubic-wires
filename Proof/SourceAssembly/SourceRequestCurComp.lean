import Proof.SourceAssembly.SourceRequestCurPrims
import Proof.SourceAssembly.SourceRequestTermSegA

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurComp
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding NearCubicWires.SourceRequest.CurPrims
open NearCubicWires.SourceFactorSel.Count (sumM mulM wordM sum_step mul_step word0_step)
noncomputable section

/-- A docked run's frame: outside the local "changed" set, the ambient is untouched. -/
theorem install_keep {t U : Nat} (sl : Fin t → Fin U) (hsl : Function.Injective sl) (A : Fin U → List Bool)
    (E E' : Fin t → List Bool) (hA : ∀ i, A (sl i) = E i) (chg : Fin t → Prop)
    (hk : ∀ i, ¬ chg i → E' i = E i) :
    ∀ z, (∀ i, chg i → sl i ≠ z) → install sl A E' z = A z := by
  intro z hz
  by_cases hp : ∃ k, sl k = z
  · obtain ⟨k, rfl⟩ := hp
    have hk' : ¬ chg k := fun h => hz k h rfl
    rw [install_slot sl hsl, hk k hk', hA]
  · exact install_other sl A E' z (by intro k hk; exact hp ⟨k, hk⟩)

/-! ## `x / J`, `x % J` -/

def divmodLocal :=
  Composition.machine (divM (0 : Fin 11) 1 2 10)
  (Composition.machine (mulM (2 : Fin 11) 1 4 10)
  (Composition.machine (wordM false (0 : Fin 11) 5 10)
  (Composition.machine (wordM false (4 : Fin 11) 6 10)
  (Composition.machine (diffM (5 : Fin 11) 6 7 10)
    (tcopyM (7 : Fin 11) 3 8 9 10)))))

def divmodCost (x : Nat) : Nat := 30 * x + 60

theorem divmod_run (x J Qa Qb S C : Nat) (E : Fin 11 → List Bool) (hJ : 0 < J) (hQb : J + 2 ≤ Qb)
    (hS : x + 2 ≤ S) (hC : 5 * x + 5 ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qa (List.replicate x true)) (h1 : E 1 = ZeroPadding.pad Qb (CompareMachine.word J))
    (hscr : ∀ j : Fin 11, 2 ≤ j.val → j.val < 10 → E j = List.replicate S false)
    (h10 : E 10 = List.replicate C false) :
    ∃ E' : Fin 11 → List Bool, Step divmodLocal (divmodCost x) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 2 = ZeroPadding.pad S (List.replicate (x / J) true) ∧
      E' 3 = ZeroPadding.pad S (List.replicate (x % J) true) ∧
      (∀ j : Fin 11, ¬ (2 ≤ j.val ∧ j.val < 10) → E' j = E j) ∧
      (∀ j : Fin 11, 2 ≤ j.val → j.val < 10 → (E' j).length = S) := by
  set q := x / J with hq
  have hqJ : q * J ≤ x := Nat.div_mul_le_self x J
  have hqx : q ≤ x := Nat.div_le_self x J
  have hmod : x % J = x - q * J := Nat.mod_eq_sub_div_mul
  have hmul : q * (2 * J + 3) + 2 ≤ C := by nlinarith
  set E1 := Function.update E 2 (ZeroPadding.pad S (List.replicate q true)) with hE1
  set E2 := Function.update E1 4 (ZeroPadding.pad S (List.replicate (q * J) true)) with hE2
  set E3 := Function.update E2 5 (ZeroPadding.pad S (CompareMachine.word x)) with hE3
  set E4 := Function.update E3 6 (ZeroPadding.pad S (CompareMachine.word (q * J))) with hE4
  set E5 := Function.update E4 7 (ZeroPadding.pad S (CompareMachine.word (x - q * J))) with hE5
  set E6 := Function.update (Function.update (Function.update E5 3
    (ZeroPadding.pad S (List.replicate (x - q * J) true))) 8 (ZeroPadding.pad S (List.replicate (x - q * J) true)))
    9 (ZeroPadding.pad S (CompareMachine.word (x - q * J))) with hE6
  have s1 := div_step (0 : Fin 11) 1 2 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    x J Qa Qb S C hJ hQb (by omega) (fun _ => 0) E (fun _ _ => rfl) h0 h1 (hscr 2 (by decide) (by decide)) h10
  have s2 := mul_step (2 : Fin 11) 1 4 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    q J S Qb S C hmul (fun _ => 0) E1 (fun _ _ => rfl) (by simp [E1]) (by simp [E1, h1])
    (by simp [E1, hscr 4 (by decide) (by decide)]) (by simp [E1, h10])
  have s3 := word0_step (0 : Fin 11) 5 10 (by decide) (by decide) (by decide) x Qa S C hS (by omega)
    (fun _ => 0) E2 (fun _ _ => rfl) (by simp [E1, E2, h0]) (by simp [E1, E2, hscr 5 (by decide) (by decide)])
    (by simp [E1, E2, h10])
  have s4 := word0_step (4 : Fin 11) 6 10 (by decide) (by decide) (by decide) (q * J) S S C (by omega) (by omega)
    (fun _ => 0) E3 (fun _ _ => rfl) (by simp [E2, E3]) (by simp [E1, E2, E3, hscr 6 (by decide) (by decide)])
    (by simp [E1, E2, E3, h10])
  have s5 := diff_step (5 : Fin 11) 6 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    x (q * J) S S S C hqJ hS (by omega) (by omega) (by omega) (fun _ => 0) E4 (fun _ _ => rfl)
    (by simp [E3, E4]) (by simp [E4]) (by simp [E1, E2, E3, E4, hscr 7 (by decide) (by decide)])
    (by simp [E1, E2, E3, E4, h10])
  have s6 := tcopy_step (7 : Fin 11) 3 8 9 10 (by decide) (x - q * J) S S C (by omega) (by omega) (by omega)
    (fun _ => 0) E5 (fun _ _ => rfl) (by simp [E5])
    (by simp [E1, E2, E3, E4, E5, hscr 3 (by decide) (by decide)])
    (by simp [E1, E2, E3, E4, E5, hscr 8 (by decide) (by decide)])
    (by simp [E1, E2, E3, E4, E5, hscr 9 (by decide) (by decide)])
    (by simp [E1, E2, E3, E4, E5, h10])
  have hall : Step divmodLocal _ _ _ _ _ := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))
  refine ⟨E6, hall.enlarge ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : q * (2 * J + 3) = 2 * (q * J) + 3 * q := by ring
    unfold divmodCost
    rw [e1]
    omega
  · simp [E1, E2, E3, E4, E5, E6]
  · simp [E1, E2, E3, E4, E5, E6, hmod]
  · intro j hj
    have hne : ∀ c : Fin 11, 2 ≤ c.val → c.val < 10 → j ≠ c := fun c h1 h2 e => hj (e ▸ ⟨h1, h2⟩)
    simp [E1, E2, E3, E4, E5, E6, hne 2 (by decide) (by decide), hne 3 (by decide) (by decide),
      hne 4 (by decide) (by decide), hne 5 (by decide) (by decide), hne 6 (by decide) (by decide),
      hne 7 (by decide) (by decide), hne 8 (by decide) (by decide), hne 9 (by decide) (by decide)]
  · intro j h2 h10'
    fin_cases j <;> simp [E1, E2, E3, E4, E5, E6, ZeroPadding.pad_length, CompareMachine.word] at h2 h10' ⊢ <;>
      omega

def divmodM {U : Nat} (sl : Fin 11 → Fin U) := RecoveryFocus.machine sl divmodLocal

/-- **`x / J` and `x % J`, docked.** -/
theorem divmod_step {U : Nat} (sl : Fin 11 → Fin U) (hsl : Function.Injective sl)
    (x J Qa Qb S C : Nat) (hJ : 0 < J) (hQb : J + 2 ≤ Qb) (hS : x + 2 ≤ S) (hC : 5 * x + 5 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ i, H (sl i) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qa (List.replicate x true))
    (h1 : A (sl 1) = ZeroPadding.pad Qb (CompareMachine.word J))
    (hscr : ∀ j : Fin 11, 2 ≤ j.val → j.val < 10 → A (sl j) = List.replicate S false)
    (h10 : A (sl 10) = List.replicate C false) :
    ∃ A' : Fin U → List Bool, Step (divmodM sl) (divmodCost x) H A H A' ∧
      A' (sl 2) = ZeroPadding.pad S (List.replicate (x / J) true) ∧
      A' (sl 3) = ZeroPadding.pad S (List.replicate (x % J) true) ∧
      (∀ z, (∀ j : Fin 11, 2 ≤ j.val → j.val < 10 → sl j ≠ z) → A' z = A z) ∧
      (∀ j : Fin 11, 2 ≤ j.val → j.val < 10 → (A' (sl j)).length = S) := by
  obtain ⟨E', st, e2, e3, ek, el⟩ := divmod_run x J Qa Qb S C (fun i => A (sl i)) hJ hQb hS hC h0 h1 hscr h10
  refine ⟨install sl A E', TermSeg.dock st sl hsl H A hH (fun _ => rfl), ?_, ?_, ?_, ?_⟩
  · rw [install_slot sl hsl, e2]
  · rw [install_slot sl hsl, e3]
  · intro z hz
    exact install_keep sl hsl A _ E' (fun _ => rfl) (fun j => 2 ≤ j.val ∧ j.val < 10) ek z
      (fun j hj => hz j hj.1 hj.2)
  · intro j h2 h10'; rw [install_slot sl hsl]; exact el j h2 h10'

/-! ## `x - y` -/

def subLocal :=
  Composition.machine (wordM false (0 : Fin 9) 3 8)
  (Composition.machine (wordM false (1 : Fin 9) 4 8)
  (Composition.machine (diffM (3 : Fin 9) 4 5 8)
    (tcopyM (5 : Fin 9) 2 6 7 8)))

def subCost (x : Nat) : Nat := 10 * x + 40

theorem sub_run (x y Qa Qb S C : Nat) (E : Fin 9 → List Bool) (hy : y ≤ x) (hS : x + 2 ≤ S) (hC : 2 * x + 5 ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qa (List.replicate x true)) (h1 : E 1 = ZeroPadding.pad Qb (List.replicate y true))
    (hscr : ∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → E j = List.replicate S false)
    (h8 : E 8 = List.replicate C false) :
    ∃ E' : Fin 9 → List Bool, Step subLocal (subCost x) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 2 = ZeroPadding.pad S (List.replicate (x - y) true) ∧
      (∀ j : Fin 9, ¬ (2 ≤ j.val ∧ j.val < 8) → E' j = E j) ∧
      (∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → (E' j).length = S) := by
  set E1 := Function.update E 3 (ZeroPadding.pad S (CompareMachine.word x)) with hE1
  set E2 := Function.update E1 4 (ZeroPadding.pad S (CompareMachine.word y)) with hE2
  set E3 := Function.update E2 5 (ZeroPadding.pad S (CompareMachine.word (x - y))) with hE3
  set E4 := Function.update (Function.update (Function.update E3 2
    (ZeroPadding.pad S (List.replicate (x - y) true))) 6 (ZeroPadding.pad S (List.replicate (x - y) true)))
    7 (ZeroPadding.pad S (CompareMachine.word (x - y))) with hE4
  have s1 := word0_step (0 : Fin 9) 3 8 (by decide) (by decide) (by decide) x Qa S C hS (by omega)
    (fun _ => 0) E (fun _ _ => rfl) h0 (hscr 3 (by decide) (by decide)) h8
  have s2 := word0_step (1 : Fin 9) 4 8 (by decide) (by decide) (by decide) y Qb S C (by omega) (by omega)
    (fun _ => 0) E1 (fun _ _ => rfl) (by simp [E1, h1]) (by simp [E1, hscr 4 (by decide) (by decide)])
    (by simp [E1, h8])
  have s3 := diff_step (3 : Fin 9) 4 5 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    x y S S S C hy hS (by omega) (by omega) (by omega) (fun _ => 0) E2 (fun _ _ => rfl)
    (by simp [E1, E2]) (by simp [E2]) (by simp [E1, E2, hscr 5 (by decide) (by decide)]) (by simp [E1, E2, h8])
  have s4 := tcopy_step (5 : Fin 9) 2 6 7 8 (by decide) (x - y) S S C (by omega) (by omega) (by omega)
    (fun _ => 0) E3 (fun _ _ => rfl) (by simp [E3])
    (by simp [E1, E2, E3, hscr 2 (by decide) (by decide)])
    (by simp [E1, E2, E3, hscr 6 (by decide) (by decide)])
    (by simp [E1, E2, E3, hscr 7 (by decide) (by decide)])
    (by simp [E1, E2, E3, h8])
  have hall : Step subLocal _ _ _ _ _ := s1.seq (s2.seq (s3.seq s4))
  refine ⟨E4, hall.enlarge ?_, ?_, ?_, ?_⟩
  · unfold subCost; omega
  · simp [E1, E2, E3, E4]
  · intro j hj
    have hne : ∀ c : Fin 9, 2 ≤ c.val → c.val < 8 → j ≠ c := fun c h1 h2 e => hj (e ▸ ⟨h1, h2⟩)
    simp [E1, E2, E3, E4, hne 2 (by decide) (by decide), hne 3 (by decide) (by decide),
      hne 4 (by decide) (by decide), hne 5 (by decide) (by decide), hne 6 (by decide) (by decide),
      hne 7 (by decide) (by decide)]
  · intro j h2 h8'
    fin_cases j <;> simp [E1, E2, E3, E4, ZeroPadding.pad_length, CompareMachine.word] at h2 h8' ⊢ <;> omega

def subM {U : Nat} (sl : Fin 9 → Fin U) := RecoveryFocus.machine sl subLocal

/-- **`x - y` (`y ≤ x`), docked.** -/
theorem sub_step {U : Nat} (sl : Fin 9 → Fin U) (hsl : Function.Injective sl)
    (x y Qa Qb S C : Nat) (hy : y ≤ x) (hS : x + 2 ≤ S) (hC : 2 * x + 5 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ i, H (sl i) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qa (List.replicate x true))
    (h1 : A (sl 1) = ZeroPadding.pad Qb (List.replicate y true))
    (hscr : ∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → A (sl j) = List.replicate S false)
    (h8 : A (sl 8) = List.replicate C false) :
    ∃ A' : Fin U → List Bool, Step (subM sl) (subCost x) H A H A' ∧
      A' (sl 2) = ZeroPadding.pad S (List.replicate (x - y) true) ∧
      (∀ z, (∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → sl j ≠ z) → A' z = A z) ∧
      (∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → (A' (sl j)).length = S) := by
  obtain ⟨E', st, e2, ek, el⟩ := sub_run x y Qa Qb S C (fun i => A (sl i)) hy hS hC h0 h1 hscr h8
  refine ⟨install sl A E', TermSeg.dock st sl hsl H A hH (fun _ => rfl), ?_, ?_, ?_⟩
  · rw [install_slot sl hsl, e2]
  · intro z hz
    exact install_keep sl hsl A _ E' (fun _ => rfl) (fun j => 2 ≤ j.val ∧ j.val < 8) ek z
      (fun j hj => hz j hj.1 hj.2)
  · intro j h2 h8'; rw [install_slot sl hsl]; exact el j h2 h8'

/-! ## The block test `[s ≤ x]` -/

def testLocal := Composition.machine (wordM false (0 : Fin 5) 3 4) (cmpM (3 : Fin 5) 1 2 4)

def testCost (s : Nat) : Nat := 4 * s + 20

theorem test_run (s x Qa Qb S C : Nat) (E : Fin 5 → List Bool) (hS : s + 2 ≤ S) (hC : s + 3 ≤ C)
    (h0 : E 0 = ZeroPadding.pad Qa (List.replicate s true)) (h1 : E 1 = ZeroPadding.pad Qb (List.replicate x true))
    (h2 : E 2 = List.replicate S false) (h3 : E 3 = List.replicate S false) (h4 : E 4 = List.replicate C false) :
    ∃ E' : Fin 5 → List Bool, Step testLocal (testCost s) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 2 = ZeroPadding.pad S [decide (s ≤ x)] ∧
      (∀ j : Fin 5, j.val ≠ 2 → j.val ≠ 3 → E' j = E j) ∧
      (E' 2).length = S ∧ (E' 3).length = S := by
  set E1 := Function.update E 3 (ZeroPadding.pad S (CompareMachine.word s)) with hE1
  set E2 := Function.update E1 2 (ZeroPadding.pad S [decide (s ≤ x)]) with hE2
  have s1 := word0_step (0 : Fin 5) 3 4 (by decide) (by decide) (by decide) s Qa S C hS hC
    (fun _ => 0) E (fun _ _ => rfl) h0 h3 h4
  have s2 := cmp_step (3 : Fin 5) 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    s x S Qb S C hS (by have := Nat.min_le_left s x; omega) (fun _ => 0) E1 (fun _ _ => rfl) (by simp [E1])
    (by simp [E1, h1]) (by simp [E1, h2]) (by simp [E1, h4])
  have hall : Step testLocal _ _ _ _ _ := s1.seq s2
  refine ⟨E2, hall.enlarge ?_, by simp [E2], ?_, ?_, ?_⟩
  · unfold testCost; have := Nat.min_le_left s x; omega
  · intro j hj2 hj3
    have n2 : j ≠ 2 := fun e => hj2 (by rw [e]; rfl)
    have n3 : j ≠ 3 := fun e => hj3 (by rw [e]; rfl)
    simp [E1, E2, n2, n3]
  · simp [E2, ZeroPadding.pad_length]; omega
  · simp [E1, E2, ZeroPadding.pad_length, CompareMachine.word]; omega

def testM {U : Nat} (sl : Fin 5 → Fin U) := RecoveryFocus.machine sl testLocal

/-- **The block test `[s ≤ x]`, docked** (local `0` `1^s`, `1` `1^x`, `2` flag, `3` scratch, `4` log). -/
theorem test_step {U : Nat} (sl : Fin 5 → Fin U) (hsl : Function.Injective sl)
    (s x Qa Qb S C : Nat) (hS : s + 2 ≤ S) (hC : s + 3 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ i, H (sl i) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qa (List.replicate s true))
    (h1 : A (sl 1) = ZeroPadding.pad Qb (List.replicate x true))
    (h2 : A (sl 2) = List.replicate S false) (h3 : A (sl 3) = List.replicate S false)
    (h4 : A (sl 4) = List.replicate C false) :
    ∃ A' : Fin U → List Bool, Step (testM sl) (testCost s) H A H A' ∧
      A' (sl 2) = ZeroPadding.pad S [decide (s ≤ x)] ∧
      (∀ z, sl 2 ≠ z → sl 3 ≠ z → A' z = A z) ∧ (A' (sl 3)).length = S := by
  obtain ⟨E', st, e2, ek, _, el3⟩ := test_run s x Qa Qb S C (fun i => A (sl i)) hS hC h0 h1 h2 h3 h4
  refine ⟨install sl A E', TermSeg.dock st sl hsl H A hH (fun _ => rfl), ?_, ?_, ?_⟩
  · rw [install_slot sl hsl, e2]
  · intro z hz2 hz3
    exact install_keep sl hsl A _ E' (fun _ => rfl) (fun j => j.val = 2 ∨ j.val = 3)
      (fun j hj => ek j (fun e => hj (Or.inl e)) (fun e => hj (Or.inr e))) z
      (by
        intro j hj
        rcases hj with h | h
        · have : j = 2 := Fin.ext h
          rw [this]; exact hz2
        · have : j = 3 := Fin.ext h
          rw [this]; exact hz3)
  · rw [install_slot sl hsl]; exact el3

/-! ## Unary copy -/

theorem copy_local (n Qa S C : Nat) (hC : n + 1 ≤ C) :
    Step PCPUnaryCopy.machine (2 * n + 4) (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate n true), List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (List.replicate n true), ZeroPadding.pad S (List.replicate n true),
        List.replicate C false] := by
  have base := Step.of_ready (PCPUnaryCopy.copy_ready n Qa S C)
  refine base.congr rfl ?_
  funext i
  fin_cases i
  · rfl
  · rfl
  · show List.replicate (max C (n + 1)) false = _
    rw [Nat.max_eq_left hC]
    rfl

def copyM {U : Nat} (a d l : Fin U) := RecoveryFocus.machine (![a, d, l] : Fin 3 → Fin U) PCPUnaryCopy.machine

/-- **Unary copy, docked** (`Function.update` of the destination). -/
theorem copy_step {U : Nat} (a d l : Fin U) (h1 : a ≠ d) (h2 : a ≠ l) (h3 : d ≠ l)
    (n Qa S C : Nat) (hC : n + 1 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ z, z = a ∨ z = d ∨ z = l → H z = 0)
    (ha : A a = ZeroPadding.pad Qa (List.replicate n true))
    (hd : A d = List.replicate S false) (hl : A l = List.replicate C false) :
    Step (copyM a d l) (2 * n + 4) H A H (Function.update A d (ZeroPadding.pad S (List.replicate n true))) :=
  SLoad.step_update (copy_local n Qa S C hC) 1
    (by intro i hi; fin_cases i <;> first | rfl | exact absurd rfl hi)
    _ (SLoad.triple_injective a d l h1 h2 h3) H A
    (by
      intro i; fin_cases i
      · exact hH _ (Or.inl rfl)
      · exact hH _ (Or.inr (Or.inl rfl))
      · exact hH _ (Or.inr (Or.inr rfl)))
    (by intro i; fin_cases i <;> assumption)

end
end NearCubicWires.SourceRequest.CurComp

