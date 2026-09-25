import Proof.Packets.PacketsXWalkLiteralProducedReserveRun
import Proof.Packets.PacketsXWalkLiteralProducedFrame

/-! Retained physical words and cursor positions needed by the majority stage. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedReserve
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open VectorBottomUp CloseoutRowsModeCache
noncomputable section
variable {population active depth n : Nat}

private theorem visit_palette (rank R L S : Nat)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool)
    (palette : Fin 15→List Bool) (work : Fin 299→List Bool) (transcript : List Bool) (j : Fin 15) :
    WalkLiteralVisit.A rank R L S v code palette work transcript ⟨15+j.val,by have hb:=j.isLt;omega⟩=palette j := by
  change WalkLiteralVisit.A rank R L S v code palette work transcript
    ((((j.castAdd 300).castAdd 1).castAdd 1).natAdd 15)=_
  simp only [WalkLiteralVisit.A,collectData,paletteData,Fin.addCases_left,Fin.addCases_right]

theorem output_palette (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) (j : Fin 15) :
    output C w root mask wins sample codeTail masters work
      ((WalkLiteralProduced.paletteSlots j).castAdd 471)=
      paddedPalette C (R C w) population root depth
        (parameters population active 0 (C+9) mask
          (WalkLiteralLoop.retainedSeed sample (WalkLiteralMasters.zeroSeed (canonicalGradedRank population active)) (n+1))) j := by
  have hs : ((WalkLiteralProduced.paletteSlots j).castAdd 471 : Fin 566)=
      (WalkLiteralProduced.coldSlots ⟨15+j.val,by have hb:=j.isLt;omega⟩).castAdd 133 := by
    rw [WalkLiteralProduced.cold_palette_slot]
    rfl
  rw [hs,output,Fin.addCases_left,install_slot WalkLiteralProduced.coldSlots WalkLiteralProduced.cold_slots_injective]
  have hj : (⟨15+j.val,by have hb:=j.isLt;omega⟩ : Fin 333)=
      (⟨15+j.val,by have hb:=j.isLt;omega⟩ : Fin 332).castAdd 1 := rfl
  rw [hj,Fin.addCases_left]
  exact visit_palette _ _ _ _ _ _ _ _ _ j

theorem output_master_words (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    output C w root mask wins sample codeTail masters work 81=ZeroPadding.pad (R C w) (UnaryTemplate.tape (2*C+3)) ∧
    output C w root mask wins sample codeTail masters work 82=ZeroPadding.pad (R C w) (UnaryTemplate.tape C) ∧
    output C w root mask wins sample codeTail masters work 71=UnaryTemplate.tape (R C w) ∧
    output C w root mask wins sample codeTail masters work 41=List.replicate (R C w) true := by
  have h0:=output_palette C w root mask wins sample codeTail masters work 0
  have h1:=output_palette C w root mask wins sample codeTail masters work 1
  have h2:=output_palette C w root mask wins sample codeTail masters work 2
  have h3:=output_palette C w root mask wins sample codeTail masters work 3
  refine ⟨h0,h1,?_,?_⟩
  · change output C w root mask wins sample codeTail masters work 71=ZeroPadding.pad (R C w) (UnaryTemplate.tape (R C w)) at h2
    have hn : R C w-(R C w+1+1)=0 := by omega
    simpa [ZeroPadding.pad,UnaryTemplate.tape,hn] using h2
  · change output C w root mask wins sample codeTail masters work 41=ZeroPadding.pad (R C w) (List.replicate (R C w) true) at h3
    simpa only [ZeroPadding.pad,List.length_replicate,Nat.sub_self,List.replicate_zero,List.append_nil] using h3

theorem output_count (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    output C w root mask wins sample codeTail masters work 427=CompareMachine.word n := by
  change output C w root mask wins sample codeTail masters work ((WalkLiteralProduced.coldSlots 332).castAdd 133)=_
  rw [output,Fin.addCases_left,install_slot WalkLiteralProduced.coldSlots WalkLiteralProduced.cold_slots_injective]
  rfl

theorem master_heads (n : Nat) : finalHeads n 81=0 ∧ finalHeads n 82=0 ∧ finalHeads n 71=0 ∧ finalHeads n 41=0 := by
  have h (j : Fin 15) : finalHeads n ((WalkLiteralProduced.paletteSlots j).castAdd 471)=0 := by
    have hs : ((WalkLiteralProduced.paletteSlots j).castAdd 471 : Fin 566)=
        (WalkLiteralProduced.coldSlots ⟨15+j.val,by have hb:=j.isLt;omega⟩).castAdd 133 := by
      rw [WalkLiteralProduced.cold_palette_slot]
      rfl
    rw [hs,finalHeads,Fin.addCases_left,WalkLiteralProduced.finalHeads,
      dockH_slot WalkLiteralProduced.coldSlots WalkLiteralProduced.cold_slots_injective]
    change WalkLiteralCold.H (160*n) 0
      (((((j.castAdd 300).castAdd 1).castAdd 1).natAdd 15).castAdd 1)=_
    simp only [WalkLiteralCold.H,WalkLiteralVisit.H,collectHeads,paletteHeads,Fin.addCases_left,Fin.addCases_right]
  exact ⟨h 0,h 1,h 2,h 3⟩

theorem count_head (n : Nat) : finalHeads n 427=1 := by
  change finalHeads n ((WalkLiteralProduced.coldSlots 332).castAdd 133)=_
  rw [finalHeads,Fin.addCases_left,WalkLiteralProduced.finalHeads,
    dockH_slot WalkLiteralProduced.coldSlots WalkLiteralProduced.cold_slots_injective]
  rfl

end
end Theorem25Completion.WalkLiteralProducedReserve
