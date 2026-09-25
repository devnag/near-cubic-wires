import Proof.Packets.ReusableArithmeticCleanup

/-! Symmetric accumulator transaction for frozen left folds. The operation
still receives (left,right) in its original order; only its output destination
changes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def resultLeft (R : Nat) (a : Fin 30 → List Bool) : Fin 30 → List Bool :=
  cleared R (replaced (replaced a 20 25) 21 28)
noncomputable def machineLeft {s : Nat} (p : Machine 30 s) :=
  Composition.machine (Composition.machine (Composition.machine (worker p)
    (copyMachine 20 25)) (copyMachine 21 28)) eraseMachine

theorem run_left {s fuel R : Nat} {p : Machine 30 s}
    {a b : Fin 30 → List Bool} {h : Fin 30 → Nat}
    (hp : Step p fuel localHeads a h b) (ha : ∀ i,(a i).length≤R) (hcap : fuel+3≤R) :
    Step (machineLeft p) (budget fuel R) heads (bank R (padded R a))
      heads (bank R (resultLeft R (padded R b))) := by
  have fits := output_fits hp ha hcap
  have first := worker_step hp hcap
  have second := copy_step R (padded R b) 20 25 (by decide) (fits _) (fits _)
  have third := copy_step R (replaced (padded R b) 20 25) 21 28 (by decide)
    (by simpa [replaced] using fits 21) (by simpa [replaced] using fits 28)
  have fourth := erase_step R (replaced (replaced (padded R b) 20 25) 21 28) (by
    intro i
    by_cases h28 : i=28
    · subst i;simpa [replaced] using (fits 21).le
    by_cases h25 : i=25
    · subst i;simpa [replaced] using (fits 20).le
    simpa [replaced,h28,h25] using (fits i).le)
  have whole := ((first.seq second).seq third).seq fourth
  convert whole using 1 <;> first | rfl | (unfold budget;omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
