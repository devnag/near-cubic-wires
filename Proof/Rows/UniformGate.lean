import Proof.Rows.FullGateRun

/-! The unchanged reusable gate evaluator accepts one uniform paid reserve R.
Only the run theorem is generalized; the same core, fanout and cleanup execute. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_UniformGate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure
open OffsetSourceGate CloseoutRowsPoolWeight
open PCJ45bee56da9f34d5a_CellGatePalette
noncomputable section
attribute [local irreducible] OffsetSourceGate.machine
theorem source_run (xs : List Item) (z : Int) (tail mtail out : List Bool) (w C D R : Nat)
    (hw : ∀ x∈xs, natBitLength x.1.natAbs ≤ w) (hc : 8*w+12 ≤ C)
    (hp : C10NaturalHardwireScore.positiveSum xs < 2^w)
    (hn : CloseoutRowsPoolMinimum.negSum xs < 2^w)
    (hD : C10NaturalHardwireScore.loopBudget xs w C ≤ D)
    (hz : natBitLength z.natAbs ≤ w)
    (hpz : C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs) < 2^w)
    (hnz : C10NaturalHardwireTarget.nPart z (C10NaturalHardwireScore.selectedSum xs) < 2^w)
    (hR : capacity xs z tail mtail w C D ≤ R) :
    Step machine (2*budget xs z w C+4*R+16) (HardwireReusable.heads out 1)
      (input xs z tail mtail w C D R out)
      (HardwireReusable.heads (out++[bit xs z]) 1)
      (input xs z tail mtail w C D R (out++[bit xs z])) := by
  obtain ⟨result,hr,_,ho⟩ := core_run xs z tail mtail out w C D hw hc hp hn hD hz hpz hnz
  have embedded := hr.embed (![0,0,1,0] : Fin 4→Nat) extra
  have h : Step worker (budget xs z w C) (HardwireChild.heads out 0 0)
      (entry xs z tail mtail w C D out)
      (HardwireChild.heads (out++[bit xs z]) ((word xs).length+(intWord z).length) xs.length)
      (Fin.addCases (motive:=fun _=>List Bool) result extra) := by
    refine (embedded.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i;fin_cases i <;>rfl
  unfold OffsetSourceGate.machine
  exact Reusable48.run worker (entry xs z tail mtail w C D) out (out++[bit xs z])
    (budget xs z w C) _ _ R _
    (by intro a j;fin_cases j <;>rfl) (by intro a;rfl) h ho
    (fun j=>(masters_fit xs z tail mtail w C D j).trans hR) (by unfold capacity at hR;omega)

end
end PCJ45bee56da9f34d5a_UniformGate
