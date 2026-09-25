import Proof.Hierarchy.CompetitorMonomialTargetWidth

/-! The exact coefficient-normalization denominator is physically widened
to the same common scalar width as every other record in the whole fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outer (i : Fin 75) : Fin 79 := i.castAdd 4
def targetHeads (out : List Bool) : Fin 79 → ℕ := fun i => if i.val=74 then out.length else 0
def denominatorSlots : Fin 5 → Fin 79 := ![75,38,76,77,78]
noncomputable def prefixProgram := RecoveryFocus.machine outer prepareProgram
noncomputable def denominatorProgram := RecoveryFocus.machine denominatorSlots ClockNormalize.machine
noncomputable def targetProgram := Composition.machine prefixProgram denominatorProgram
def targetBudget (b t : ℕ) := prepareBudget b t+4*t+5

theorem outer_injective : Function.Injective outer := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 79 => a.val) h)
theorem outer_other (j : Fin 75) (i : Fin 79) (hi : 75 ≤ i.val) : outer j≠i := by
  intro h
  have hv := congrArg (fun a : Fin 79 => a.val) h
  change j.val=i.val at hv
  omega

end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
