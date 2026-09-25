import Proof.MachineModel.BlockUnaryCalc

namespace NearCubicWires.BlockPlatform
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
open RepairOrdinary.RecoveryRootRound NearCubicWires.ExtDecompositionBatch
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem dockH_existing {t u : ℕ} (slots : Fin t → Fin u) (ambient : Fin u → ℕ)
    (local' : Fin t → ℕ) (h : ∀ j, ambient (slots j) = local' j) :
    dockH slots ambient local' = ambient := by
  funext i
  cases hp : RecoveryFocus.pick slots i with
  | none => simp [dockH, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slots hp
    simp only [dockH, hp]
    rw [← he]
    exact (h j).symm

namespace Scrub




end Scrub

/-- **The whole loop as one `Step`**, so an entry composes with it by `Step.seq`. The loop's
own entry is `Cells.run`'s: the data bank extended by the counter `CompareMachine.word bound`
(head `1`); `RepeatMachine.cfg 0`'s control is the loop machine's start. -/
theorem Cells.loopStep {t s : ℕ} (c : Cells t s) (out : List Bool) :
    Step (CloseoutRowsDegreeLoop.machine c.body) (c.bound*(c.cost+3)+3)
      (Fin.addCases (c.source 0 out).heads (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source 0 out).tapes (fun _ : Fin 1 => CompareMachine.word c.bound))
      (Fin.addCases (c.source c.bound (out ++ (List.range c.bound).flatMap c.emit)).heads
        (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source c.bound (out ++ (List.range c.bound).flatMap c.emit)).tapes
        (fun _ : Fin 1 => CompareMachine.word c.bound)) := by
  obtain ⟨r, hr, hf, _⟩ := c.run out
  refine Step.of_run (r := r) hr ?_ ?_
  · rw [hf]; rfl
  · rw [hf]; rfl

end
end NearCubicWires.BlockPlatform
