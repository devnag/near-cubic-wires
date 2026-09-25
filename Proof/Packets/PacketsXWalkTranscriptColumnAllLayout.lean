import Proof.Packets.PacketsXWalkTranscriptColumnBounds

/-! Candidate-order state for the genuine remaining-column loop. Clamping
is only a totalization beyond the terminal index; every executed candidate
is proved to be its actual finite index. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumn
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section
variable {population active depth n : Nat}

def allColumn (population k : Nat) : Fin (population+1) := ⟨min k population,by omega⟩
theorem allColumn_val (population k : Nat) (hk : k≤population) :
    (allColumn population k).val=k := Nat.min_eq_left hk

theorem allColumn_at (i : Fin (population+1)) : allColumn population i.val=i := by
  apply Fin.ext
  exact allColumn_val population i.val (by omega)

def allPolys (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (k : Nat) := coordinates mask wins sample (allColumn population k)
def allPacket (C : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (k : Nat) := (Normalized.structuralMaskedWalkListCoordinate mask (canonicalGradedLabel population active)
      wins 0 sample (allColumn population k)).map (maskNat C)
def allLast (C : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (k : Nat) := (coordinate mask wins sample (allColumn population k) n).map (maskNat C)
def allResult (C R : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (k : Nat) := TranscriptColumn.columnPrefix R (allPacket C mask wins sample) k

theorem allPolys_length (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (k : Nat) : (allPolys mask wins sample k).length=n+1 := List.length_ofFn

theorem allPacket_majority (C : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (k : Nat) : (MajorityComplete.majority (allPolys mask wins sample k)).map (maskNat C)=allPacket C mask wins sample k := by
  exact congrArg (fun P=>P.map (maskNat C)) (majority_exact mask wins sample (allColumn population k))

theorem allResult_succ (C R : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (k : Nat) : allResult C R mask wins sample (k+1)=allResult C R mask wins sample k++
      PacketVector.entry R (allPacket C mask wins sample k) := TranscriptColumn.prefix_succ R _ k

theorem allResult_final (C R : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1)) :
    allResult C R mask wins sample (population+1)=PacketVector.bank R
      (List.ofFn (fun column : Fin (population+1)=>
        (Normalized.structuralMaskedWalkListCoordinate mask (canonicalGradedLabel population active)
          wins 0 sample column).map (maskNat C))) := by
  rw [allResult,TranscriptColumn.prefix_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext column
  simp only [allPacket,allColumn_at]

theorem allLast_fits (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (k : Nat) : PacketVector.Fits (commonReserve C w) (allLast C mask wins sample k) := by
  have actual:=TranscriptColumn.rowPacket_fits (commonReserve C w) (population+1)
    (WalkLiteralLoop.rows C mask wins sample) (WalkLiteralLoop.rows_length C mask wins sample)
    (allColumn population k) (WalkLiteralLoop.rows_fits C w d root S L mask wins h sample) n
  simpa only [row_packet,allLast] using actual

end
end Theorem25Completion.WalkTranscriptColumn
