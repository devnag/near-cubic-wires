import Proof.Packets.SubstitutionOuterData

/-! An actual outer-fold transaction: transfer the current monomial product,
add it on the left of the resident sum, save the sum, then restore product one.
The original source, atom table, count drivers, and constant one are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

noncomputable def transfer := RecoveryFocus.machine accumulatorPorts VectorAccumulator.rightToLeft
noncomputable def add := RecoveryFocus.machine accumulatorPorts VectorAccumulator.machineRight
noncomputable def reset := RecoveryFocus.machine constantPorts VectorAccumulator.loadRight
noncomputable def accumulate := Composition.machine transfer (Composition.machine add reset)
def accumulateBudget (C R : Nat) (product stored : Packet) :=
  VectorAccumulator.copyBudget R+1+(VectorAccumulator.budget C R product stored+1+VectorAccumulator.copyBudget R)

theorem accumulate_run (C R index position : Nat) (left product stored : Packet) (atoms source : List Bool)
    (hl : VectorAccumulator.Fits R left) (hp : VectorAccumulator.Fits R product)
    (hs : VectorAccumulator.Fits R stored) (ho : VectorAccumulator.Fits R (one C))
    (hwProduct : ∀ bits∈product,bits.length=C) (hwStored : ∀ bits∈stored,bits.length=C)
    (ha : ∀ i,(ReusableArithmetic.data C product stored i).length≤R)
    (hcap : NormalizedAddition.budget C product stored+3≤R) :
    Step accumulate (accumulateBudget C R product stored)
      (H position 1) (A C R index left product atoms source stored)
      (H position 1) (A C R index product (one C) atoms source (VectorAccumulator.answer product stored)) := by
  have first:=dock_accumulator C R index position 1 left product stored product product stored atoms source
    (VectorAccumulator.right_to_left_run C R left product stored hl hp)
  have second:=dock_accumulator C R index position 1 product product stored product
    (VectorAccumulator.answer product stored) (VectorAccumulator.answer product stored) atoms source
    (VectorAccumulator.run_right C R product product stored hp hs hwProduct hwStored ha hcap)
  have resultFit:=VectorAccumulator.answer_fits C R product stored hwProduct hwStored ha hcap
  have third:=dock_constant C R index position 1 product (VectorAccumulator.answer product stored)
    product (one C) (VectorAccumulator.answer product stored) atoms source
    (VectorAccumulator.load_right_run C R product (VectorAccumulator.answer product stored) (one C) resultFit ho)
  exact first.seq (second.seq third)

theorem accumulate_bound (C R : Nat) (product stored : Packet)
    (hcap : NormalizedAddition.budget C product stored≤R) :
    accumulateBudget C R product stored≤48*(R+1) := by
  unfold accumulateBudget VectorAccumulator.budget VectorAccumulator.copyBudget ReusableArithmetic.budget
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
