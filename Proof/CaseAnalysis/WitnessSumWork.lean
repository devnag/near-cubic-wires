import Proof.CaseAnalysis.WitnessSumCursor

/-! The complete term loop and final mass decision run beside the retained
sum parser bank. Only the actual count driver carries its already-paid
zero allocation; no record stream is padded or copied at this join. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumWork
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def heads (position driver : ℕ) (out native counts : List Bool) : Fin 3061 → ℕ :=
  Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>ℕ)
    (SumDock.coreHeads position driver out native) (SumCountStream.heads counts)
def data (P H b core W L K : ℕ) (source out native : List Bool)
    (ambient : Fin 94 → List Bool) (extra : Fin 528 → List Bool) : Fin 3061 → List Bool :=
  Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>List Bool)
    (SumDock.coreData P H b core W L source out native
      (ZeroPadding.pad H (CompareMachine.word K)) true ambient) extra
def pads (H : ℕ) (i : Fin 2533) := if i=2532 then H else 0

private theorem padded_data (H : ℕ) (left : Fin 2532 → List Bool) (driver : List Bool) :
    (fun i=>ZeroPadding.pad (pads H i)
      (Fin.addCases (m:=2532) (n:=1) (motive:=fun _=>List Bool) left (fun _=>driver) i))=
    Fin.addCases (m:=2532) (n:=1) (motive:=fun _=>List Bool) left (fun _=>ZeroPadding.pad H driver) := by
  funext i
  refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ i
  · intro j
    have hj : j.castAdd 1≠(2532 : Fin 2533) := by intro h;have hv:=congrArg Fin.val h;change j.val=2532 at hv;omega
    simp only [Fin.addCases_left,pads,if_neg hj,ZeroPadding.pad_zero]
  · intro j
    fin_cases j
    simp only [Fin.addCases_right]
    rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumWork
