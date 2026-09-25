import Proof.Packets.PacketsXWalkTranscriptColumnCandidate

/-! Specialize the direct candidate transaction to the original masked walk
polynomials. Every row, column, majority term, and appended packet keeps the
original normalized constructor order. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds WalkTranscriptColumnArena
noncomputable section
variable {population active depth n : Nat}

theorem walk_worker_run (palette : Fin 10→List Bool) (C w d root S L : Nat)
    (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (column : Fin (population+1)) (old : PacketVector.Packet)
    (oldFits : PacketVector.Fits (commonReserve C w) old) (result : List Bool)
    (hfit : (population+1)^(d*(n+1))≤2^w) (hVisits : n+1≤2^w) (hCodes : 2^(n+1)≤2^w)
    (hc : MajorityComplete.Bootstrap.Compatible palette C (commonReserve C w) (n+1) ((commonReserve C w)^2))
    (H : Fin 471→Nat) (A : Fin 471→List Bool) (hh : ReadyHeads H result.length)
    (ha : Ready palette C (commonReserve C w) ((commonReserve C w)^2) (population+1) (n+1) S column.val
      (PacketTranscript.prefixBank (commonReserve C w) (WalkLiteralLoop.rows C mask wins sample) (n+1)) old
      (List.replicate ((n+1)*(2*commonReserve C w)) false) result (coordinates mask wins sample column) A) :
    let R:=commonReserve C w
    let next:=result++PacketVector.entry R
      ((Normalized.structuralMaskedWalkListCoordinate mask (canonicalGradedLabel population active)
        wins 0 sample column).map (maskNat C))
    ∃B,Step worker (workerBudget C w (population+1) (n+1) column.val) H A (Function.update H 29 next.length) B ∧
      Ready palette C R (R^2) (population+1) (n+1) S (column.val+1)
        (PacketTranscript.prefixBank R (WalkLiteralLoop.rows C mask wins sample) (n+1))
        ((coordinate mask wins sample column n).map (maskNat C))
        (List.replicate ((n+1)*(2*R)) false) next (coordinates mask wins sample column) B ∧
      ReadyHeads (Function.update H 29 next.length) next.length := by
  have hpop : population≤C := by
    have hsq : depth+2*population+2≤(depth+2*population+2)^2 := by
      rw [pow_two]
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (depth+2*population+2)
        (by omega : 1≤depth+2*population+2)
    exact (by omega : population≤depth+2*population+2).trans (hsq.trans h.codeCapacity)
  have hs : ∀j∈Finset.range population,j<C := by
    intro j hj
    have hjp:=Finset.mem_range.mp hj
    omega
  have hlen : (coordinates mask wins sample column).length=n+1 := List.length_ofFn
  have actual:=worker_run palette C w (population+1) (n+1) S (Finset.range population) d
    (WalkLiteralLoop.rows C mask wins sample) (WalkLiteralLoop.rows_length C mask wins sample)
    column old (WalkLiteralLoop.rows_fits C w d root S L mask wins h sample) oldFits result
    (coordinates mask wins sample column) hs (coordinates_bounded C w d root S L mask wins h sample column)
    (by simpa only [Finset.card_range,hlen] using hfit)
    (by simpa only [Finset.card_range] using h.source)
    (by simpa only [hlen] using hVisits) (by simpa only [hlen] using hCodes)
    (by have hw:=h.width;omega) hlen hc (column_packets C mask wins sample column) H A hh ha
  simpa only [majority_exact,TranscriptColumn.previous_succ,row_packet] using actual

end
end Theorem25Completion.WalkTranscriptColumn
