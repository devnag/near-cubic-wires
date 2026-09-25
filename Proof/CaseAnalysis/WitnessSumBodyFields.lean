import Proof.CaseAnalysis.WitnessTermLoopMeaning

/-! The existing final mass test acts on the retained term bank. Both
embeddings use the original nested layout, so no tape copy or vector
reassociation is executed. The literal term driver is retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumBody
open LocalBitMultitape CompetitorSumFold RepairSource.VerifierDecoding
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def ending (k : ℕ) (q : ℚ) :=
  TapeEmbedding.machine 1 (TapeEmbedding.machine 1705 (SumFinish.machine k q))
def heads (position : ℕ) (out : List Bool) (extra : Fin 1705 → ℕ) : Fin 2533 → ℕ :=
  Fin.addCases (m:=2532) (n:=1) (motive:=fun _=>ℕ) (TermRound.heads position out extra) (fun _=>1)
def data (P K : ℕ) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (out : List Bool) (extra : Fin 1705 → List Bool) : Fin 2533 → List Bool :=
  Fin.addCases (m:=2532) (n:=1) (motive:=fun _=>List Bool) (TermRound.data P terms ambient out extra)
    (fun _=>CompareMachine.word K)

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumBody
