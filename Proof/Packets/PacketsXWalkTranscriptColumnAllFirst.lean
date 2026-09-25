import Proof.Packets.PacketsXWalkTranscriptColumnWalkStep
import Proof.Packets.PacketsXWalkTranscriptColumnAllLayout

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

def allHeads (H : Fin 471→Nat) (C R : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (i : Nat) := Function.update H 29 (allResult C R mask wins sample (i+1)).length

theorem all_first_run (palette : Fin 10→List Bool) (C w d root S L : Nat)
    (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (hfit : (population+1)^(d*(n+1))≤2^w) (hVisits : n+1≤2^w) (hCodes : 2^(n+1)≤2^w)
    (hc : MajorityComplete.Bootstrap.Compatible palette C (commonReserve C w) (n+1) ((commonReserve C w)^2))
    (H : Fin 471→Nat) (A : Fin 471→List Bool) (hh : ReadyHeads H 0)
    (ha : Ready palette C (commonReserve C w) ((commonReserve C w)^2) (population+1) (n+1) S 0
      (PacketTranscript.prefixBank (commonReserve C w) (WalkLiteralLoop.rows C mask wins sample) (n+1))
      (allLast C mask wins sample 0) (OrderedPacketStep.bank C (commonReserve C w) (allPolys mask wins sample 0))
      [] (allPolys mask wins sample 0) A) :
    let R:=commonReserve C w
    ∃B,Step candidate (candidateBudget C w (n+1) 0) H A (allHeads H C R mask wins sample 0) B ∧
      Ready palette C R (R^2) (population+1) (n+1) S 1
        (PacketTranscript.prefixBank R (WalkLiteralLoop.rows C mask wins sample) (n+1))
        (allLast C mask wins sample 0) (List.replicate ((n+1)*(2*R)) false)
        (allResult C R mask wins sample 1) (allPolys mask wins sample 1) B ∧
      ReadyHeads (allHeads H C R mask wins sample 0) (allResult C R mask wins sample 1).length := by
  dsimp only
  have hpop : population≤C := by
    have hsq : depth+2*population+2≤(depth+2*population+2)^2 := by
      rw [pow_two]
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (depth+2*population+2)
        (by omega : 1≤depth+2*population+2)
    exact (by omega : population≤depth+2*population+2).trans (hsq.trans h.codeCapacity)
  have hs : ∀j∈Finset.range population,j<C := by
    intro j hj;have hjp:=Finset.mem_range.mp hj;omega
  have hlen := allPolys_length mask wins sample 0
  have hw : 1≤w := by have hw:=h.width;omega
  have hpf:=MajorityComplete.palette_fits C w (n+1) hVisits hCodes hw
  obtain ⟨B,actual,ready,heads⟩:=candidate_run palette C w (population+1) (n+1) S 0 (Finset.range population) d
    _ _ [] (allLast C mask wins sample 0) (allPolys mask wins sample 0) hs
    (coordinates_bounded C w d root S L mask wins h sample (allColumn population 0))
    (by simpa only [Finset.card_range,hlen] using hfit)
    (by simpa only [Finset.card_range] using h.source)
    (by simpa only [hlen] using hVisits) (by simpa only [hlen] using hCodes) hw hlen hc H A hh ha rfl
  have hpkt:=allPacket_majority C mask wins sample 0
  have he : []++PacketVector.entry (commonReserve C w) (allPacket C mask wins sample 0)=
      allResult C (commonReserve C w) mask wins sample 1 := by
    rw [allResult_succ]
    rfl
  rw [hpkt,he] at actual ready heads
  refine ⟨B,actual,?_,heads⟩
  exact ready.change_polys hpf.reserve (by have hd:=hpf.arithmetic;omega)
    (by rw [allPolys_length,allPolys_length])

end
end Theorem25Completion.WalkTranscriptColumn
