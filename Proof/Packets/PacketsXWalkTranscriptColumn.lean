import Proof.Packets.TranscriptColumnProgram
import Proof.Packets.PacketsXWalkLiteralLoopData

/-! The physical column extractor applied to the exact literal walk
transcript. Its output is the increasing-time list of the paper's normalized
coordinate polynomials, with each polynomial's literal list order retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds VectorBottomUp
noncomputable section
variable {population active depth n : Nat}

def coordinate (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) (time : Nat) :=
  Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active)
    (WalkLiteralLoop.seedAt sample time) wins 0 column

def coordinates (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) :=
  List.ofFn (fun time : Fin (n+1)=>coordinate mask wins sample column time.val)

theorem row_packet (C : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) (time : Nat) :
    TranscriptColumn.rowPacket (population+1) (WalkLiteralLoop.rows C mask wins sample)
      (WalkLiteralLoop.rows_length C mask wins sample) column time=
      (coordinate mask wins sample column time).map (maskNat C) := by
  simp only [TranscriptColumn.rowPacket,WalkLiteralLoop.rows,literalCoordinatePackets,coordinate,List.getElem_ofFn]

theorem column_packets (C : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) :
    List.ofFn (fun time : Fin (n+1)=>
      TranscriptColumn.rowPacket (population+1) (WalkLiteralLoop.rows C mask wins sample)
        (WalkLiteralLoop.rows_length C mask wins sample) column time.val)=
      (coordinates mask wins sample column).map (fun P=>P.map (maskNat C)) := by
  simp only [row_packet,coordinates,List.map_ofFn,Function.comp_def]

end
end Theorem25Completion.WalkTranscriptColumn
