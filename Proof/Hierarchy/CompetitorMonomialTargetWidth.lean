import Proof.Hierarchy.CompetitorDimensions

namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 67) : Fin 75 := i.castAdd 8
def widenSlots : Fin 9 → Fin 75 := ![67,10,24,68,69,70,71,72,73]
def heads (out : List Bool) : Fin 75 → ℕ := fun i => if i.val=74 then out.length else 0
noncomputable def productsProgram := RecoveryFocus.machine native CompetitorRationalDecision.productsProgram
noncomputable def widenProgram := RecoveryFocus.machine widenSlots CompetitorNumeratorWiden.machine
noncomputable def prepareProgram := Composition.machine productsProgram widenProgram
def prepareBudget (b t : ℕ) := 2000*(b+1)^2+8*width t+10

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 75 => a.val) h)
theorem native_other (j : Fin 67) (i : Fin 75) (hi : 67 ≤ i.val) : native j≠i := by
  intro h
  have hv := congrArg (fun a : Fin 75 => a.val) h
  change j.val=i.val at hv
  omega
theorem product_fit (b a c : ℕ) (ha : a<2^b) (hc : c<2^b) : a*c<2^width b :=
  (Nat.mul_le_mul_left a hc.le).trans_lt (scalar_fit b a ha)

end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
