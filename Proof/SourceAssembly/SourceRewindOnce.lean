import Proof.SourceAssembly.SourceRowWidth

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction.RewindOnce
noncomputable section

def c1 : Fin 4 → Fin 7 := ![0, 1, 2, 3]
def c2 : Fin 4 → Fin 7 := ![0, 4, 5, 6]
def mask : Fin 7 → Bool := fun i => i.val = 5

def machine :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine c1 ClockUnarySum.machine)
    (RecoveryFocus.machine c2 ClockUnarySum.machine))
    (CloseoutWitness.SelectedErase.machine mask (2 : Fin 7) (3 : Fin 7))

def cost (V : ℕ) : ℕ := ((2*V+6)+1+(2*V+6))+1+(2*V+4)

def input (V : ℕ) : Fin 7 → List Bool := fun i => if i.val = 0 then List.replicate V true else []

theorem c1_inj : Function.Injective c1 := by decide
theorem c2_inj : Function.Injective c2 := by decide

theorem rewind_run (V : ℕ) : ∃ W : Fin 7 → List Bool,
    Step machine (cost V) (fun _ => 0) (input V) (fun _ => 0) W ∧
    W 2 = List.replicate V true ∧ W 5 = List.replicate V false ∧ W 0 = List.replicate V true := by
  let o : Fin 4 → List Bool := ![List.replicate V true, [], List.replicate V true,
    List.replicate (V+2) false]
  have s1 := Dimension.dock0 (BlockPlatform.UnaryCalc.copy_step V) c1 c1_inj (input V) (by
    intro j
    fin_cases j <;> rfl)
  let B1 := install c1 (input V) o
  have s2 := Dimension.dock0 (BlockPlatform.UnaryCalc.copy_step V) c2 c2_inj B1 (by
    intro j
    fin_cases j
    · exact install_slot c1 c1_inj (input V) o 0
    · exact install_other c1 (input V) o _ (by decide)
    · exact install_other c1 (input V) o _ (by decide)
    · exact install_other c1 (input V) o _ (by decide))
  let B2 := install c2 B1 o
  have B2_2 : B2 2 = List.replicate V true :=
    (install_other c2 B1 o _ (by decide)).trans (install_slot c1 c1_inj (input V) o 2)
  have B2_3 : B2 3 = List.replicate (V+2) false :=
    (install_other c2 B1 o _ (by decide)).trans (install_slot c1 c1_inj (input V) o 3)
  have B2_5 : B2 5 = List.replicate V true := install_slot c2 c2_inj B1 o 2
  have B2_0 : B2 0 = List.replicate V true := install_slot c2 c2_inj B1 o 0
  have s3 := BlockPlatform.Scrub.erase_step mask (2 : Fin 7) (3 : Fin 7) (by decide) (by decide)
    (by decide) V (V+2) (by omega) (fun _ => 0) B2 (fun _ _ => rfl) (by
      intro i hi
      have h5 : i = 5 := Fin.ext (by simpa [mask] using hi)
      rw [h5, B2_5]
      simp) B2_2 B2_3
  refine ⟨BlockPlatform.Scrub.blank mask B2 V, (s1.seq s2).seq s3, ?_, ?_, ?_⟩
  · simp only [BlockPlatform.Scrub.blank, show mask 2 = false by decide, Bool.false_eq_true, if_false]
    exact B2_2
  · simp [BlockPlatform.Scrub.blank, mask]
  · simp only [BlockPlatform.Scrub.blank, show mask 0 = false by decide, Bool.false_eq_true, if_false]
    exact B2_0

end
end NearCubicWires.SourceConstruction.RewindOnce
end
