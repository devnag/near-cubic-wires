import Proof.Packets.PacketsXWalkLiteralProducedMajorityProjection

/-! Concrete column input facts from the actual walk and scalar outputs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open VectorBottomUp CloseoutRowsModeCache
noncomputable section
variable {population active depth n : Nat}
attribute [local irreducible] walkBank walkHeads WalkLiteralProducedReserve.output
  WalkLiteralProducedReserve.finalHeads WalkLiteralProduced.finalHeads

theorem scalar_column_pin (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool)
    (hR : 1≤R C w) (hRS : R C w≤S C w) (ready : TranscriptRewindReady (R C w) (S C w) (population+1) work) :
    ∀i,scalarBank C (R C w) n (zeroBank (S C w) (walkBank C w root mask wins sample codeTail masters work)) (columnSlots i)=
      TranscriptColumn.residentTapes (R C w) (population+1) (n+1) 0 (S C w)
        (PacketTranscript.prefixBank (R C w) (WalkLiteralLoop.rows C mask wins sample) (n+1))
        (PacketVector.payload (R C w) []) (PacketVector.count (R C w) []) [] i := by
  have six:=six_column_pin (R C w) (S C w) (population+1) n
    (walkBank C w root mask wins sample codeTail masters work)
    (PacketTranscript.prefixBank (R C w) (WalkLiteralLoop.rows C mask wins sample) (n+1))
    (PacketVector.payload (R C w) []) (PacketVector.count (R C w) [])
    ((walk_work_word C w root mask wins sample codeTail masters work 31).trans ready.width)
    (walk_transcript_word C w root mask wins sample codeTail masters work)
    ((walk_work_word C w root mask wins sample codeTail masters work 257).trans
      (ready.payload.trans (TranscriptColumn.empty_payload (R C w) (S C w) hRS).symm))
    ((walk_work_word C w root mask wins sample codeTail masters work 263).trans
      (ready.zero.trans (TranscriptColumn.empty_count (R C w) (S C w) hR hRS).symm))
    ((walk_work_word C w root mask wins sample codeTail masters work 297).trans ready.count)
    ((walk_work_word C w root mask wins sample codeTail masters work 261).trans ready.scratch)
  exact scalar_zero_column C (R C w) (S C w) (population+1) n _ _ _ _ (hR.trans hRS) six

end
end Theorem25Completion.WalkLiteralProducedMajority
