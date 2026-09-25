import Proof.Packets.PacketsXVectorCollectReady
import Proof.Packets.PacketsXVectorLiteralPaddedPaletteProgram

/-! Complete literal-vector construction followed by paid append of every
coordinate, preserving its exact ordinal and polynomial list ordering. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.ExtIncidence
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section


def literalCoordinatePackets (C population active depth : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population active)) (wins : Fin depth → Nat) :=
  List.ofFn (fun candidate : Fin (population+1)=>
    (Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active)
      seed wins 0 candidate).map (maskNat C))
attribute [local irreducible] literalPaletteProgram collectMachine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
