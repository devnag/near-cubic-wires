import Proof.Packets.PacketsXWalkLiteralProducedMajorityStart
import Proof.Packets.PacketsXWalkLiteralProducedMajorityResidentLayout

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

theorem walk_cold_word (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) (j : Fin 333) :
    walkBank C w root mask wins sample codeTail masters work ((WalkLiteralProduced.coldSlots j).castAdd 309)=
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralLoop.A C w root (S C w) (R C w) mask wins sample
          (WalkLiteralMasters.zeroSeed (canonicalGradedRank population active)) codeTail [] [] (n+1) work)
        (fun _=>CompareMachine.word n)) j := by
  have hs : ((WalkLiteralProduced.coldSlots j).castAdd 309 : Fin 742)=
      ((WalkLiteralProduced.coldSlots j).castAdd 133).castAdd 176 := rfl
  rw [hs,walkBank,Fin.addCases_left,WalkLiteralProducedReserve.output,Fin.addCases_left,
    install_slot WalkLiteralProduced.coldSlots WalkLiteralProduced.cold_slots_injective]

theorem walk_cold_head (n : Nat) (j : Fin 333) :
    walkHeads n ((WalkLiteralProduced.coldSlots j).castAdd 309)=WalkLiteralCold.H (160*n) 0 j := by
  have hs : ((WalkLiteralProduced.coldSlots j).castAdd 309 : Fin 742)=
      ((WalkLiteralProduced.coldSlots j).castAdd 133).castAdd 176 := rfl
  rw [hs,walkHeads,Fin.addCases_left,WalkLiteralProducedReserve.finalHeads,Fin.addCases_left,
    WalkLiteralProduced.finalHeads,dockH_slot WalkLiteralProduced.coldSlots WalkLiteralProduced.cold_slots_injective]

theorem scalar_column_heads (n : Nat) :
    ∀i,scalarHeads (walkHeads n) (columnSlots i)=columnStartHeads i := by
  have outside (i : Fin 9) (h6:i≠6) (h7:i≠7) :
      scalarHeads (walkHeads n) (columnSlots i)=walkHeads n (columnSlots i) := by
    apply dockH_other
    intro j he
    rcases column_cold_overlap i j he.symm with hp|hp
    · exact h6 hp.1
    · exact h7 hp.1
  intro i;fin_cases i
  · change scalarHeads (walkHeads n) (columnSlots 0)=columnStartHeads 0
    rw [outside 0 (by decide) (by decide)];exact walk_cold_head n 61
  · change scalarHeads (walkHeads n) (columnSlots 1)=columnStartHeads 1
    rw [outside 1 (by decide) (by decide)];exact walk_cold_head n 331
  · change scalarHeads (walkHeads n) (columnSlots 2)=columnStartHeads 2
    rw [outside 2 (by decide) (by decide)];exact walk_cold_head n 287
  · change scalarHeads (walkHeads n) (columnSlots 3)=columnStartHeads 3
    rw [outside 3 (by decide) (by decide)];exact walk_cold_head n 293
  · change scalarHeads (walkHeads n) (columnSlots 4)=columnStartHeads 4
    rw [outside 4 (by decide) (by decide)];exact walk_cold_head n 327
  · change scalarHeads (walkHeads n) (columnSlots 5)=columnStartHeads 5
    rw [outside 5 (by decide) (by decide)];exact walk_cold_head n 291
  · change scalarHeads (walkHeads n) (columnSlots 6)=columnStartHeads 6
    exact dockH_slot coldSlots cold_injective (walkHeads n) (fun _=>0) 44
  · change scalarHeads (walkHeads n) (columnSlots 7)=columnStartHeads 7
    exact dockH_slot coldSlots cold_injective (walkHeads n) (fun _=>0) 146
  · change scalarHeads (walkHeads n) (columnSlots 8)=columnStartHeads 8
    rw [outside 8 (by decide) (by decide)]
    change walkHeads n ((1 : Fin 176).natAdd 566)=_
    rw [walkHeads,Fin.addCases_right]
    rfl

theorem walk_work_word (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) (j : Fin 299) :
    walkBank C w root mask wins sample codeTail masters work
      ((WalkLiteralProduced.coldSlots ((((((j.castAdd 1).natAdd 15).castAdd 1).castAdd 1).natAdd 15).castAdd 1)).castAdd 309)=work j := by
  apply (walk_cold_word C w root mask wins sample codeTail masters work _).trans
  simp only [WalkLiteralLoop.A,WalkLiteralVisit.A,collectData,paletteData,Fin.addCases_left,Fin.addCases_right]

theorem walk_transcript_word (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    walkBank C w root mask wins sample codeTail masters work 426=
      PacketTranscript.prefixBank (R C w) (WalkLiteralLoop.rows C mask wins sample) (n+1) := by
  apply (walk_cold_word C w root mask wins sample codeTail masters work 331).trans
  change WalkLiteralLoop.transcript (R C w) (WalkLiteralLoop.stride C w population) (n+1)
    (WalkLiteralLoop.rows C mask wins sample) [] [] (n+1)=_
  simp only [WalkLiteralLoop.transcript,Nat.sub_self,Nat.zero_mul,List.replicate_zero,List.nil_append,List.append_nil]

end
end Theorem25Completion.WalkLiteralProducedMajority
