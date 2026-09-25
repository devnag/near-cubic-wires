import Proof.Hierarchy.CompetitorMonomialTargetDenominator

/-! Whole actual coefficient/count-to-term producer. It computes the three
exact integer products, widens all fields to the global width, and appends the literal
negative/positive/denominator record consumed by the cold rational fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorRawFieldEmit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sources : List (Fin 79) := [71,68,76]
def fields (t : ℕ) (a : CompetitorValidity.Estimate) : Fin 79 → List Bool := fun i =>
  if i.val=71 then binary (width t) a.negative
  else if i.val=68 then binary (width t) a.positive
  else if i.val=76 then binary t a.denominator else []
noncomputable def emitProgram := listProgram (74 : Fin 79) 70 sources
noncomputable def machine := Composition.machine targetProgram emitProgram
def budget (b t : ℕ) := targetBudget b t+20*t+29

theorem stream_eq (t : ℕ) (a : CompetitorValidity.Estimate) :
    stream (fields t a) sources=CompetitorSumFold.termWord t a := by
  simp [stream,fields,sources,CompetitorSumFold.termWord,CompetitorSumFold.fieldStream,
    CompetitorSumFold.termFields,CompetitorSumFold.termTargets]
theorem cost_eq (t : ℕ) (a : CompetitorValidity.Estimate) : listCost (fields t a) sources=20*t+28 := by
  simp [listCost,fields,sources,width]
  omega

theorem budget_bound (b t : ℕ) (htarget : width b≤t) : budget b t≤2500*(t+1)^2 := by
  have hbt : b≤t := by unfold width at htarget; omega
  unfold budget targetBudget prepareBudget width
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
