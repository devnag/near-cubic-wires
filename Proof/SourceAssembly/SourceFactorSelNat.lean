import Proof.SourceAssembly.SourceFactorSelDesc
import Proof.SourceAssembly.SourceFactorSelHeader

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Nat
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation
noncomputable section

open CloseoutRowsEstimatorParity

def natM := Composition.machine (Desc.copyM (22 : Fin 25) 0 23 24) (TapeEmbedding.machine 3 Natural.machine)

def natCost (n D : Nat) : Nat := 2 * D + 4 + 1 + Natural.budget n

theorem nat_local (n Qb Q Qd D C S : Nat) (hn : n ≤ Qb)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value Qb ≤ S) (hnD : n ≤ D) (hDS : D ≤ S) (hC : D + 1 ≤ C)
    (E : Fin 25 → List Bool) (h22 : E 22 = ZeroPadding.pad Q (List.replicate n true))
    (h23 : E 23 = ZeroPadding.pad Qd (List.replicate D true)) (h24 : E 24 = List.replicate C false)
    (hscr : ∀ j : Fin 25, j.val < 22 → E j = List.replicate S false) :
    ∃ E' : Fin 25 → List Bool,
      Step natM (natCost n D) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 20 = ZeroPadding.pad S (frame (natWord n)) ∧
      (∀ j : Fin 25, 22 ≤ j.val → E' j = E j) ∧
      (∀ j : Fin 25, j.val < 22 → (E' j).length = S) := by
  have s1 := Desc.copy_step (22 : Fin 25) 0 23 24 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) Q Qd D C S (List.replicate n true) (by simpa using hnD) hDS hC
    (fun _ => 0) E rfl rfl rfl rfl h22 (hscr 0 (by decide)) h23 h24
  set E1 := Function.update E 0 (ZeroPadding.pad S (List.replicate n true)) with hE1
  obtain ⟨out, hready, h20, _, hlen⟩ := Natural.native_run Qb n hn
  have hnat := (SLoad.MaskFrame.step_of_clockReady hready).pad (fun _ => S)
  have hemb := hnat.embed (fun _ : Fin 3 => 0) (fun j : Fin 3 => E1 (Fin.natAdd 22 j))
  have hz : (Fin.addCases (motive := fun _ => Nat) (fun _ : Fin 22 => 0) (fun _ : Fin 3 => 0) :
      Fin (22 + 3) → Nat) = fun _ => 0 := by
    funext j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;>
      simp only [Fin.addCases_left, Fin.addCases_right]
  rw [hz] at hemb
  have hin : (Fin.addCases (motive := fun _ => List Bool)
      (fun i => ZeroPadding.pad S (Natural.input Qb n i)) (fun j : Fin 3 => E1 (Fin.natAdd 22 j)) :
      Fin (22 + 3) → List Bool) = E1 := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.addCases_left]
      simp only [Natural.input, Natural.source]
      rw [Desc.pad_pad (CloseoutRowsEstimatorParity.Capacity.value Qb) S _ hcap]
      by_cases h0 : i = 0
      · subst h0
        simp [hE1]
      · rw [if_neg h0, hE1, Function.update_of_ne]
        · rw [hscr _ (by simp)]
          simp [ZeroPadding.pad]
        · intro e
          apply h0
          apply Fin.ext
          have := congrArg Fin.val e
          simpa using this
    · rw [Fin.addCases_right]
  rw [hin] at hemb
  refine ⟨_, s1.seq hemb, ?_, ?_, ?_⟩
  · show Fin.addCases (motive := fun _ => List Bool) (fun i => ZeroPadding.pad S (out i))
      (fun j : Fin 3 => E1 (Fin.natAdd 22 j)) (Fin.castAdd 3 (20 : Fin 22)) = _
    rw [Fin.addCases_left, h20, Desc.pad_pad _ S _ hcap]
  · intro j hj
    have e : j = Fin.natAdd 22 (⟨j.val - 22, by omega⟩ : Fin 3) := Fin.ext (by simp; omega)
    rw [e]
    show Fin.addCases (motive := fun _ => List Bool) (fun i => ZeroPadding.pad S (out i))
      (fun j : Fin 3 => E1 (Fin.natAdd 22 j)) (Fin.natAdd 22 _) = _
    rw [Fin.addCases_right, hE1, Function.update_of_ne]
    intro e'
    have := congrArg Fin.val e'
    simp at this
  · intro j hj
    have e : j = Fin.castAdd 3 (⟨j.val, hj⟩ : Fin 22) := Fin.ext rfl
    rw [e]
    show (Fin.addCases (motive := fun _ => List Bool) (fun i => ZeroPadding.pad S (out i))
      (fun j : Fin 3 => E1 (Fin.natAdd 22 j)) (Fin.castAdd 3 _)).length = _
    rw [Fin.addCases_left, ZeroPadding.pad_length, hlen]
    omega

/-- **`1^n ↦ frame (natWord n)`, docked** by an injective `sl : Fin 25 → Fin U` (`sl 22` the unary resident,
`sl 23` driver `1^D`, `sl 24` log `0^C`, `sl 0..21` blank `S`-cell scratch, output on `sl 20`). -/
theorem nat_step {U : Nat} (sl : Fin 25 → Fin U) (hsl : Function.Injective sl)
    (n Qb Q Qd D C S : Nat) (hn : n ≤ Qb)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value Qb ≤ S) (hnD : n ≤ D) (hDS : D ≤ S) (hC : D + 1 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h22 : A (sl 22) = ZeroPadding.pad Q (List.replicate n true))
    (h23 : A (sl 23) = ZeroPadding.pad Qd (List.replicate D true)) (h24 : A (sl 24) = List.replicate C false)
    (hscr : ∀ j : Fin 25, j.val < 22 → A (sl j) = List.replicate S false) :
    ∃ A' : Fin U → List Bool,
      Step (RecoveryFocus.machine sl natM) (natCost n D) H A H A' ∧
      A' (sl 20) = ZeroPadding.pad S (frame (natWord n)) ∧
      (∀ j : Fin 25, 22 ≤ j.val → A' (sl j) = A (sl j)) ∧
      (∀ j : Fin 25, j.val < 22 → (A' (sl j)).length = S) ∧
      (∀ x, (∀ j, sl j ≠ x) → A' x = A x) := by
  obtain ⟨E', hs, h20, hkeep, hlen⟩ := nat_local n Qb Q Qd D C S hn hcap hnD hDS hC (fun j => A (sl j))
    h22 h23 h24 hscr
  have d := hs.dock sl hsl H A (fun j => hH j) (fun j => rfl)
  rw [dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_, ?_, ?_⟩
  · rw [install_slot sl hsl]; exact h20
  · intro j hj; rw [install_slot sl hsl]; exact hkeep j hj
  · intro j hj; rw [install_slot sl hsl]; exact hlen j hj
  · intro x hx; exact install_other sl A E' x hx

/-! ## The mode tag -/

/-- The header's first field (`1` THR, `0` SYM), framed. -/
def tagWord (mode : Bool) : List Bool := frame (natWord (if mode then 0 else 1))

theorem tagWord_length (mode : Bool) : (tagWord mode).length = 7 := by
  cases mode <;> decide

theorem pair_injective {U : Nat} (d l : Fin U) (h : d ≠ l) : Function.Injective (![d, l] : Fin 2 → Fin U) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij h | exact absurd hij.symm h


end
end NearCubicWires.SourceFactorSel.Nat
