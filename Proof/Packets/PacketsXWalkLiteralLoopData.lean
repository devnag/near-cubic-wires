import Proof.Packets.PacketsXWalkLiteralAdvance
import Proof.Packets.PacketTranscript
import Proof.Packets.PhysicalRepeatExistsHeads

/-! Concrete counted-walk state: original vertex and seed, resident bounded
workspace, exact ordered transcript prefix, and remaining allocated zeros. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
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

structure Bounds (C w d population active depth root S L : Nat) (wins : Fin depth → Nat) : Prop where
  depthRank : depth≤canonicalGradedRank population active
  rankPopulation : canonicalGradedRank population active≤9*population
  populationCapacity : (258*population+2)^2≤C
  codeCapacity : (depth+2*population+2)^2≤C
  populationPositive : 1≤population
  populationRank : population≤2^(canonicalGradedRank population active)
  width : 3≤w
  degree : structuralListCoordinateRawDegree depth wins 0≤d
  literals : (population*(2*depth+1)+2)^d≤2^w
  source : (population+1)^d≤2^w
  atoms : population+1≤2^w
  windows : ∀level,wins level=GradedWindow.window root level.val
  windowBound : ∀level,wins level≤64*(C+2)
  rootBound : root+67≤commonReserve C w
  reserve : commonReserve C w+3≤S
  capacity : 2*C+5≤S
  space : literalInitializedFuel C w population root depth+2≤S
  rankPositive : 0<canonicalGradedRank population active
  decode : 8*canonicalGradedRank population active+14≤commonReserve C w
  labels : 2*toeplitzWalkSideBits (canonicalGradedRank population active)+1≤L

variable {population active depth n : Nat}

def seedAt {rank n : Nat} (sample : MargulisWalkSample (2^toeplitzWalkSideBits rank) (n+1)) (i : Nat) :=
  (toeplitzWalkEncoding rank (WalkTimeLoop.vertex sample i)).1

def retainedSeed {rank n : Nat} (sample : MargulisWalkSample (2^toeplitzWalkSideBits rank) (n+1))
    (old : ToeplitzSeed rank) (i : Nat) := if i=0 then old else seedAt sample (i-1)

theorem retained_succ {rank n : Nat} (sample : MargulisWalkSample (2^toeplitzWalkSideBits rank) (n+1))
    (old : ToeplitzSeed rank) (i : Nat) : retainedSeed sample old (i+1)=seedAt sample i := by
  simp [retainedSeed]

def rows (C : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (i : Nat) := literalCoordinatePackets C population active depth mask (seedAt sample i) wins

def stride (C w population : Nat) := (population+1)*(2*commonReserve C w)

def transcript (R block N : Nat) (rows : Nat→List PacketVector.Packet) (base tail : List Bool) (i : Nat) :=
  base++PacketTranscript.prefixBank R rows i++List.replicate ((N-i)*block) false++tail

def H (C w population n : Nat) (base : List Bool) (i : Nat) :=
  WalkLiteralVisit.H (160*min i n) (base.length+i*stride C w population)

def A (C w root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (old : ToeplitzSeed (canonicalGradedRank population active)) (codeTail base tail : List Bool)
    (i : Nat) (work : Fin 299 → List Bool) :=
  WalkLiteralVisit.A (canonicalGradedRank population active) (commonReserve C w) L S
    (WalkTimeLoop.vertex sample i) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
    (paddedPalette C (commonReserve C w) population root depth
      (parameters population active 0 (C+9) mask (retainedSeed sample old i))) work
    (transcript (commonReserve C w) (stride C w population) (n+1) (rows C mask wins sample) base tail i)

def body := Composition.machine WalkLiteralVisit.machine WalkLiteralAdvance.machine

def visitFuel (C w population active root depth S : Nat) :=
  WalkLiteralVisit.budget (canonicalGradedRank population active) C w population root depth S

def bodyFuel (C w population active root depth S : Nat) :=
  visitFuel C w population active root depth S+1+
    WalkLiteralAdvance.budget (canonicalGradedRank population active) (commonReserve C w)

theorem rows_length (C : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (i : Nat) : (rows C mask wins sample i).length=population+1 := List.length_ofFn

theorem rows_fits (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (h : Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (i : Nat) : ∀P∈rows C mask wins sample i,PacketVector.Fits (commonReserve C w) P := by
  intro P hP
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hP
  exact packet_fits _ _ (literal_coordinate_guards C w d population active depth mask (seedAt sample i) wins j
    h.depthRank h.codeCapacity h.degree h.source h.literals).2.2.2

theorem word_input (R block N : Nat) (rows : Nat→List PacketVector.Packet) (base tail : List Bool)
    (i : Nat) (hi : i<N) :
    (base++PacketTranscript.prefixBank R rows i)++List.replicate block false++
      (List.replicate ((N-(i+1))*block) false++tail)=transcript R block N rows base tail i := by
  rw [transcript,PacketTranscript.remaining_split N i block hi]
  simp only [List.append_assoc]

theorem word_output (R block N : Nat) (rows : Nat→List PacketVector.Packet) (base tail : List Bool) (i : Nat) :
    (base++PacketTranscript.prefixBank R rows i)++PacketVector.bank R (rows i)++
      (List.replicate ((N-(i+1))*block) false++tail)=transcript R block N rows base tail (i+1) := by
  rw [transcript,PacketTranscript.prefix_succ]
  simp only [List.append_assoc]

end
end Theorem25Completion.WalkLiteralLoop
