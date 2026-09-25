import Proof.Rows.FinalNativeResidue

/-! One physical native signed coefficient is reduced and appended in the
actual modular row's framed summand grammar. The original source cursor is
retained; this does not clear the scalar workspace for the next coefficient. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueAppend
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2 → Fin 23 := ![14,22]
noncomputable def last := RecoveryFocus.machine slots CloseoutRowsTouching.FrameStream.machine

def budget (negate : Bool) (z : ℤ) (w : ℕ) := C10NativeResidue.budget negate z w+1+(2*w+1)

/-- The append order is the exact order consumed by `sourceCfg`/`loopStart`. -/
theorem blocks_snoc (words : ℕ → List Bool) (j : ℕ) :
    FinalPrimeModular.blocks words 0 j ++ frame (words j) = FinalPrimeModular.blocks words 0 (j+1) := by
  simpa only [Nat.zero_add,FinalPrimeModular.blocks,List.append_nil] using
    (FinalPrimeModular.blocks_add words 0 j 1).symm

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueAppend
