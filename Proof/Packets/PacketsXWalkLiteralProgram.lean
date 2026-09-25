import Proof.Packets.PacketsXWalkLiteralResident
import Proof.Packets.PacketsXWalkLiteralJoined

/-! A complete cold walk-transcript program. Vector workspace, walk scratch,
rewind logs and the transcript are physically created from empty tapes. -/
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

def entryHeads : Fin 333→Nat :=
  Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>1)
def entry (rank R S n : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (palette : Fin 15→List Bool) : Fin 333→List Bool :=
  Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=15) (n:=317) (motive:=fun _=>List Bool) (residentInput rank R v code)
      (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>List Bool) (NativeFanout.input (m:=299) palette S) (fun _=>[])))
    (fun _=>CompareMachine.word n)
def residentArena := TapeEmbedding.machine 1 (TapeEmbedding.machine 317 residentMachine)

theorem resident_arena_run (rank R S n : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (palette : Fin 15→List Bool) :
    Step residentArena (2*R+6) entryHeads (entry rank R S n v code palette)
      coldHeads (coldInput rank R S R n v code palette) := by
  have first:=(resident_run rank R v code).embed (fun _ : Fin 317=>0)
    (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>List Bool) (NativeFanout.input (m:=299) palette S) (fun _=>[]))
  have second:=first.embed (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word n)
  have heads : Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat)
      (Fin.addCases (m:=15) (n:=317) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)) (fun _=>1)=entryHeads := by
    congr 1
    funext i
    refine Fin.addCases (m:=15) (n:=317) (fun j=>?_) (fun j=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]
  have output_heads : Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat)
      (Fin.addCases (m:=15) (n:=317) (motive:=fun _=>Nat) (WalkSeedResident.heads 0) (fun _=>0))
      (fun _=>1)=coldHeads := by
    unfold coldHeads
    congr 2
    funext i
    refine Fin.addCases (m:=316) (n:=1) (fun j=>?_) (fun j=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]
  exact (second.congr_in heads rfl).congr output_heads rfl

def program := Composition.machine residentArena machine
def programBudget (C w population active root depth S n : Nat) :=
  2*commonReserve C w+7+budget C w population active root depth S n
attribute [local irreducible] residentArena machine

theorem program_run (C w d root S : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S (commonReserve C w) wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (old : ToeplitzSeed (canonicalGradedRank population active)) (codeTail : List Bool) :
    ∃out,Step program (programBudget C w population active root depth S n) entryHeads
      (entry (canonicalGradedRank population active) (commonReserve C w) S n
        (WalkTimeLoop.vertex sample 0) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
        (paddedPalette C (commonReserve C w) population root depth (parameters population active 0 (C+9) mask old)))
      (H (160*n) 0)
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralLoop.A C w root S (commonReserve C w) mask wins sample old codeTail [] [] (n+1) out)
        (fun _=>CompareMachine.word n)) ∧
      (∀j,(out j).length≤S) ∧ TranscriptRewindReady (commonReserve C w) S (population+1) out := by
  have first:=resident_arena_run (canonicalGradedRank population active) (commonReserve C w) S n
    (WalkTimeLoop.vertex sample 0) (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
    (paddedPalette C (commonReserve C w) population root depth (parameters population active 0 (C+9) mask old))
  obtain ⟨out,last,hout,ready⟩:=run C w d root S (commonReserve C w) mask wins h sample old codeTail
  have joined:=first.seq last
  refine ⟨out,?_,hout,ready⟩
  simpa only [program,programBudget,show 2*commonReserve C w+6+1=2*commonReserve C w+7 by omega] using joined

end
end Theorem25Completion.WalkLiteralCold
