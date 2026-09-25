import Proof.Rows.UniformGate

/-! Consume the same resident-master fanout/evaluator/erase program with a
single uniform reserve, so consecutive original gates share exactly one bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_UniformGateCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure
open PCJ45bee56da9f34d5a_CellGatePalette PCJ45bee56da9f34d5a_CellGate
noncomputable section
attribute [local irreducible] OffsetSourceGate.machine
theorem evaluate_run (xs : List CloseoutRowsPoolWeight.Item) (z : Int)
    (tail mtail out : List Bool) (w C D R U : Nat)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hp : C10NaturalHardwireScore.positiveSum xs<2^w)
    (hn : CloseoutRowsPoolMinimum.negSum xs<2^w)
    (hD : C10NaturalHardwireScore.loopBudget xs w C≤D)
    (hz : natBitLength z.natAbs≤w)
    (hpz : C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs)<2^w)
    (hnz : C10NaturalHardwireTarget.nPart z (C10NaturalHardwireScore.selectedSum xs)<2^w)
    (hCU : C+1≤U) (hDU : D≤U)
    (hRU : R+1≤U)
    (hcap : OffsetSourceGate.capacity xs z tail mtail w C D ≤ R) :
    let palette:=words (CloseoutRowsPoolWeight.word xs++intWord z++tail)
      (CloseoutRowsPoolWeight.mask xs++mtail) xs.length w C R
    Step evaluate (2*OffsetSourceGate.budget xs z w C+4*R+16)
      (heads out 1) (warm palette U out)
      (heads (out++[OffsetSourceGate.bit xs z]) 1)
      (warm palette U (out++[OffsetSourceGate.bit xs z])) := by
  have hp := (PCJ45bee56da9f34d5a_UniformGate.source_run xs z tail mtail out w C D R hw hc hp hn hD hz hpz hnz hcap).pad (caps U)
  have h := hp.dock gates gates_injective (heads out 1)
    (warm (words (CloseoutRowsPoolWeight.word xs++intWord z++tail)
      (CloseoutRowsPoolWeight.mask xs++mtail) xs.length w C
      (R)) U out)
    (head_gate out 1) (fun j=>(input_pad xs z tail mtail out w C D _ U hCU hDU hRU j).symm)
  exact h.congr (dock_heads _ _ _ _) (install_warm _ _ _ _ _
    (input_pad xs z tail mtail _ w C D _ U hCU hDU hRU))

theorem run (xs : List CloseoutRowsPoolWeight.Item) (z : Int)
    (tail mtail out : List Bool) (w C D R U : Nat)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hp : C10NaturalHardwireScore.positiveSum xs<2^w)
    (hn : CloseoutRowsPoolMinimum.negSum xs<2^w)
    (hD : C10NaturalHardwireScore.loopBudget xs w C≤D)
    (hz : natBitLength z.natAbs≤w)
    (hpz : C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs)<2^w)
    (hnz : C10NaturalHardwireTarget.nPart z (C10NaturalHardwireScore.selectedSum xs)<2^w)
    (hCU : C+1≤U) (hDU : D≤U)
    (hRU : R+1≤U)
    (hcap : OffsetSourceGate.capacity xs z tail mtail w C D ≤ R)
    (hU : ∀i,(words (CloseoutRowsPoolWeight.word xs++intWord z++tail)
      (CloseoutRowsPoolWeight.mask xs++mtail) xs.length w C
      (R) i).length≤U) :
    let palette:=words (CloseoutRowsPoolWeight.word xs++intWord z++tail)
      (CloseoutRowsPoolWeight.mask xs++mtail) xs.length w C R
    Step machine (2*OffsetSourceGate.budget xs z w C+4*R+4*U+30)
      (heads out 0) (cold palette U out)
      (heads (out++[OffsetSourceGate.bit xs z]) 0)
      (cold palette U (out++[OffsetSourceGate.bit xs z])) := by
  have eval:=evaluate_run xs z tail mtail out w C D R U hw hc hp hn hD hz hpz hnz hCU hDU hRU hcap
  have h:=(fanout_run _ U out hU).seq ((move_run true _ U out).seq
    (eval.seq ((move_run false _ U _).seq (wipe_run _ U _ hU))))
  rw [show (2*U+4)+1+(1+1+((2*OffsetSourceGate.budget xs z w C+
      4*R+16)+1+(1+1+(2*U+4))))=
      2*OffsetSourceGate.budget xs z w C+4*R+4*U+30
      by omega] at h
  exact h

end
end PCJ45bee56da9f34d5a_UniformGateCell
