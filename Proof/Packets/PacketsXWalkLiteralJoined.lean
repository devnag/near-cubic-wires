import Proof.Packets.PacketsXWalkLiteralPrepare

/-! The physical walk collector starts with empty vector work tapes and an
empty transcript, builds their storage, and returns the complete ordered bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open VectorBottomUp CloseoutRowsModeCache Theorem25Completion.CycleBounds
noncomputable section
variable {population active depth n : Nat}

theorem word_bounds (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (old : ToeplitzSeed (canonicalGradedRank population active))
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins) :
    ColdWordBounds C (commonReserve C w) population root depth
      (parameters population active 0 (C+9) mask old) := by
  have hsmall : 258*population+2≤C :=
    (show 258*population+2≤(258*population+2)^2 from Nat.le_self_pow (by decide) _).trans h.populationCapacity
  have hdepth : depth+2*population+2≤C :=
    (show depth+2*population+2≤(depth+2*population+2)^2 from Nat.le_self_pow (by decide) _).trans h.codeCapacity
  have hrank:=h.rankPopulation
  have hroot:=h.rootBound
  exact cold_original_word_bounds C w population active root depth mask old (by omega) (by omega) (by omega) (by omega)

def machine := Composition.machine prepare WalkTranscriptRewind.collectedMachine
def budget (C w population active root depth S n : Nat) :=
  prepareBudget (commonReserve C w) S population n+1+
    WalkTranscriptRewind.collectedBudget C w population active root depth S n
attribute [local irreducible] prepare WalkTranscriptRewind.collectedMachine

theorem run (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (old : ToeplitzSeed (canonicalGradedRank population active)) (codeTail : List Bool) :
    ∃out,Step machine (budget C w population active root depth S n) coldHeads
      (coldInput (canonicalGradedRank population active) (commonReserve C w) S L n
        (WalkTimeLoop.vertex sample 0) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
        (paddedPalette C (commonReserve C w) population root depth (parameters population active 0 (C+9) mask old)))
      (H (160*n) 0)
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralLoop.A C w root S L mask wins sample old codeTail [] [] (n+1) out)
        (fun _=>CompareMachine.word n)) ∧
      (∀j,(out j).length≤S) ∧ TranscriptRewindReady (commonReserve C w) S (population+1) out := by
  have bounds:=word_bounds C w d root S L mask wins old h
  have first:=prepare_run C (commonReserve C w) population root depth S L
    (canonicalGradedRank population active) n (parameters population active 0 (C+9) mask old)
    (WalkTimeLoop.vertex sample 0) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
    bounds h.reserve h.capacity
  have hwork : ∀j,(work (commonReserve C w) S (population+1) j).length≤S := by
    apply work_length
    · have hr:=h.reserve;omega
    · have hr:=h.reserve;have hp:=bounds.population;omega
  obtain ⟨out,last,hout,ready⟩:=WalkTranscriptRewind.collected_run C w d root S L mask wins h sample old
    codeTail [] [] (work (commonReserve C w) S (population+1)) hwork
  have data : A (canonicalGradedRank population active) (commonReserve C w) S L n
      (WalkTimeLoop.vertex sample 0) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
      (paddedPalette C (commonReserve C w) population root depth (parameters population active 0 (C+9) mask old))
      (work (commonReserve C w) S (population+1))
      (List.replicate ((n+1)*((population+1)*(2*commonReserve C w))) false)=
      Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralLoop.A C w root S L mask wins sample old codeTail [] [] 0
          (work (commonReserve C w) S (population+1))) (fun _=>CompareMachine.word n) := by
    simp only [A,WalkLiteralLoop.A,WalkLiteralLoop.retainedSeed,if_pos rfl,if_true,
      WalkLiteralLoop.transcript,PacketTranscript.prefix_zero,WalkLiteralLoop.stride,Nat.sub_zero,
      List.nil_append,List.append_nil]
  have heads : H 0 0=Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat)
      (WalkLiteralLoop.H C w population n [] 0) (fun _=>1) := by
    simp only [H,WalkLiteralLoop.H,Nat.zero_min,Nat.mul_zero,List.length_nil,Nat.zero_mul,Nat.zero_add]
  rw [data,heads] at first
  have joined:=first.seq last
  exact ⟨out,joined,hout,ready⟩

end
end Theorem25Completion.WalkLiteralCold
