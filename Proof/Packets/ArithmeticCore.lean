import Proof.Packets.Arithmetic

/-! Exact reusable arithmetic endpoint of the physical cold bootstrap. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.ProjectionNormalization
open Theorem25Completion

theorem zero_count (R : Nat) (hR : 1 ≤ R) :
    ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
  simp only [CompareMachine.word,List.replicate_zero]
  change List.replicate 1 false++List.replicate (R-1) false=List.replicate R false
  rw [←List.replicate_add]
  congr 1
  omega

theorem output_core (C R : Nat) (hR : 1 ≤ R) (i : Fin 34) :
    output C R (i.castAdd 12)=ReusableArithmetic.state C R [] [] i := by
  fin_cases i <;>
    simp [output,widthed,CycleArithmeticAllocate.output,CycleArithmeticAllocate.bank2,
      ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,
      ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,
      NormalizeCold.data,Normalize.records,SuffixScan.stream,Fin.addCases,
      zero_count R hR,ZeroPadding.pad]
  all_goals exact (zero_count R hR).symm

theorem heads_core (i : Fin 34) : heads (i.castAdd 12)=ReusableArithmetic.heads i := by
  fin_cases i <;>rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticCold
