import Proof.Packets.PacketsXWalkLiteralProducedRun
import Proof.Packets.PacketsXWalkLiteralProducedEntry

/-! The actual produced walk also retains the scalar and mask source words.
This strengthens the existing run without changing its machine or fuel. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open VectorBottomUp CloseoutRowsModeCache Theorem25Completion.CycleBounds
noncomputable section
variable {population active depth n : Nat}
attribute [local irreducible] entryMachine WalkLiteralCold.program

theorem run_retained (C w d root S : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S (commonReserve C w) wins)
    (hdepth : depth=SourceGradedRank.depth active)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) :
    ∃masters out,Step machine (budget C w root population active depth S n (List.ofFn (fun i=>decide (i∈mask))))
      (fun _=>0)
      (input C (commonReserve C w) root population active S n (List.ofFn (fun i=>decide (i∈mask)))
        (coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
        (coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
        (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail))
      (finalHeads n)
      (install coldSlots
        (prepared masters (canonicalGradedRank population active) (commonReserve C w) S n
          (coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
          (coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
          (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail))
        (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
          (WalkLiteralLoop.A C w root S (commonReserve C w) mask wins sample
            (WalkLiteralMasters.zeroSeed (canonicalGradedRank population active)) codeTail [] [] (n+1) out)
          (fun _=>CompareMachine.word n))) ∧
      (∀j,(out j).length≤S) ∧ TranscriptRewindReady (commonReserve C w) S (population+1) out ∧
      Retained C (commonReserve C w) root population active (List.ofFn (fun i=>decide (i∈mask))) masters := by
  have fits:=WalkLiteralMasters.original_bounds C w d root S (commonReserve C w) mask wins h
  have gradedFits:=fits
  rw [hdepth] at gradedFits
  have coordFits (a : ZMod (2^toeplitzWalkSideBits (canonicalGradedRank population active))) :
      (coordinate (canonicalGradedRank population active) a).length≤commonReserve C w := by
    rw [coordinate_length];exact h.labels
  obtain ⟨masters,first,pins,retained⟩:=retained_entry_run C (commonReserve C w) root population active S n
    (List.ofFn (fun i=>decide (i∈mask)))
    (coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
    (coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
    (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
    gradedFits (coordFits _) (coordFits _)
  have palettePins : ∀i,masters (paletteSlots i)=
      paddedPalette C (commonReserve C w) population root depth
        (parameters population active 0 (C+9) mask (WalkLiteralMasters.zeroSeed (canonicalGradedRank population active))) i := by
    intro i
    rw [pins,←hdepth]
    exact congrFun (WalkLiteralMasters.palette_eq_original C (commonReserve C w) population active root depth mask
      (by have hr:=fits.rank;omega)) i
  obtain ⟨out,last,hout,ready⟩:=WalkLiteralCold.program_run C w d root S mask wins h sample
    (WalkLiteralMasters.zeroSeed (canonicalGradedRank population active)) codeTail
  have focused:=last.focus coldSlots cold_slots_injective preparedHeads
    (prepared masters (canonicalGradedRank population active) (commonReserve C w) S n
      (coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).1)
      (coordinate (canonicalGradedRank population active) (WalkTimeLoop.vertex sample 0).2)
      (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail))
  have boundary:=prepared_join masters (canonicalGradedRank population active) (commonReserve C w) S n
    (WalkTimeLoop.vertex sample 0) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
    _ palettePins
  have lastStep:=focused.congr_in prepared_heads_dock (install_existing _ _ _ boundary)
  refine ⟨masters,out,?_,hout,ready,retained⟩
  simpa only [machine,walkMachine,budget,finalHeads] using first.seq lastStep

end
end Theorem25Completion.WalkLiteralProduced
