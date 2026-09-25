import Proof.Packets.PacketsXWalkLiteralLoopData

/-! Every counted walk iteration executes the actual visit and actual
transition. The final visit consumes the last remaining transcript block. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed.Materializer
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds
open VectorBottomUp SubstitutionCensus
noncomputable section
variable {population active depth n : Nat}
attribute [local irreducible] WalkLiteralVisit.machine WalkLiteralAdvance.machine

theorem visit (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (h : Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (old : ToeplitzSeed (canonicalGradedRank population active)) (codeTail base tail : List Bool)
    (i : Nat) (hi : i≤n) (work : Fin 299 → List Bool) (hw : ∀j,(work j).length≤S) :
    ∃out,Step WalkLiteralVisit.machine (visitFuel C w population active root depth S)
      (H C w population n base i) (A C w root S L mask wins sample old codeTail base tail i work)
      (WalkLiteralVisit.H (160*i) (base.length+(i+1)*stride C w population))
      (WalkLiteralVisit.A (canonicalGradedRank population active) (commonReserve C w) L S
        (WalkTimeLoop.vertex sample i) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
        (paddedPalette C (commonReserve C w) population root depth
          (parameters population active 0 (C+9) mask (seedAt sample i))) out
        (transcript (commonReserve C w) (stride C w population) (n+1) (rows C mask wins sample) base tail (i+1))) ∧
      (∀j,(out j).length≤S) ∧ TranscriptRewindReady (commonReserve C w) S (population+1) out := by
  let R:=commonReserve C w
  let block:=stride C w population
  let pre:=base++PacketTranscript.prefixBank R (rows C mask wins sample) i
  let rest:=List.replicate ((n+1-(i+1))*block) false++tail
  obtain ⟨out,step,hlen,_,hready⟩:=WalkLiteralVisit.run C w d population active depth root S L (160*i)
    mask (retainedSeed sample old i) wins h.depthRank h.rankPopulation h.populationCapacity h.codeCapacity
    h.populationPositive h.populationRank h.width h.degree h.literals h.source h.atoms h.windows
    h.windowBound h.rootBound h.reserve h.capacity h.space work hw pre rest h.rankPositive h.decode
    (WalkTimeLoop.vertex sample i) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
  have hp : pre.length=base.length+i*block := by
    dsimp only [pre]
    rw [List.length_append,PacketTranscript.prefix_length R (population+1) _
      (rows_length C mask wins sample) (rows_fits C w d root S L mask wins h sample)]
    rfl
  change Step WalkLiteralVisit.machine (visitFuel C w population active root depth S)
    (WalkLiteralVisit.H (160*i) pre.length)
    (WalkLiteralVisit.A (canonicalGradedRank population active) R L S (WalkTimeLoop.vertex sample i)
      (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
      (paddedPalette C R population root depth (parameters population active 0 (C+9) mask (retainedSeed sample old i)))
      work (pre++List.replicate block false++rest))
    (WalkLiteralVisit.H (160*i) (pre.length+block))
    (WalkLiteralVisit.A (canonicalGradedRank population active) R L S (WalkTimeLoop.vertex sample i)
      (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
      (paddedPalette C R population root depth (parameters population active 0 (C+9) mask (seedAt sample i)))
      out (pre++PacketVector.bank R (rows C mask wins sample i)++rest)) at step
  rw [hp] at step
  dsimp only [pre,rest] at step
  rw [word_input R block (n+1) (rows C mask wins sample) base tail i (by omega),
    word_output R block (n+1) (rows C mask wins sample) base tail i] at step
  have dest : base.length+i*block+block=base.length+(i+1)*block := by ring
  rw [dest] at step
  refine ⟨out,?_,hlen,hready⟩
  simpa only [H,A,Nat.min_eq_left hi] using step

theorem iteration (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (h : Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (old : ToeplitzSeed (canonicalGradedRank population active)) (codeTail base tail : List Bool)
    (i : Nat) (hi : i<n) (work : Fin 299 → List Bool) (hw : ∀j,(work j).length≤S) :
    ∃out,Step body (bodyFuel C w population active root depth S)
      (H C w population n base i) (A C w root S L mask wins sample old codeTail base tail i work)
      (H C w population n base (i+1)) (A C w root S L mask wins sample old codeTail base tail (i+1) out) ∧
      (∀j,(out j).length≤S) ∧ TranscriptRewindReady (commonReserve C w) S (population+1) out := by
  obtain ⟨out,first,hlen,hready⟩:=visit C w d root S L mask wins h sample old codeTail base tail i (by omega) work hw
  have side:=twice_toeplitzWalkSideBits_le (canonicalGradedRank population active)
  have bits:=toeplitzSeedBits_le_three_mul (canonicalGradedRank population active)
  have hdecode:=h.decode
  have second:=WalkLiteralAdvance.run (commonReserve C w) L S (base.length+(i+1)*stride C w population)
    sample codeTail (paddedPalette C (commonReserve C w) population root depth
      (parameters population active 0 (C+9) mask (seedAt sample i))) out
    (transcript (commonReserve C w) (stride C w population) (n+1) (rows C mask wins sample) base tail (i+1))
    i hi (by omega) h.labels
  have joined:=first.seq second
  refine ⟨out,?_,hlen,hready⟩
  simpa only [body,bodyFuel,H,A,retained_succ,Nat.min_eq_left (by omega : i+1≤n)] using joined

theorem final_visit (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (h : Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (old : ToeplitzSeed (canonicalGradedRank population active)) (codeTail base tail : List Bool)
    (work : Fin 299 → List Bool) (hw : ∀j,(work j).length≤S) :
    ∃out,Step WalkLiteralVisit.machine (visitFuel C w population active root depth S)
      (H C w population n base n) (A C w root S L mask wins sample old codeTail base tail n work)
      (H C w population n base (n+1)) (A C w root S L mask wins sample old codeTail base tail (n+1) out) ∧
      (∀j,(out j).length≤S) ∧ TranscriptRewindReady (commonReserve C w) S (population+1) out := by
  obtain ⟨out,step,hlen,hready⟩:=visit C w d root S L mask wins h sample old codeTail base tail n le_rfl work hw
  refine ⟨out,?_,hlen,hready⟩
  simpa only [H,A,retained_succ,WalkTimeLoop.vertex,Nat.min_self,
    Nat.min_eq_right (by omega : n≤n+1)] using step

end
end Theorem25Completion.WalkLiteralLoop
