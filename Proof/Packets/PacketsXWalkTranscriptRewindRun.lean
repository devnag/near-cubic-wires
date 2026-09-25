import Proof.Packets.PacketsXWalkTranscriptRewindRow

/-! A counted return across all `n+1` rows of a positive walk transcript.
The existing physical count word is reused and restored. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptRewind
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer
open VectorBottomUp
noncomputable section

def machine := Composition.machine (RepeatMachine.machine row (fun _ _=>true))
  (TapeEmbedding.machine 1 row)
def budget (R N n : Nat) := n*(PacketVectorRewind.budget R N+3)+4+PacketVectorRewind.budget R N
attribute [local irreducible] row

theorem run (rank R S L N n position pos : Nat)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool)
    (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) (transcript : List Bool)
    (hRS : R≤S) (ready : TranscriptRewindReady R S N work) :
    Step machine (budget R N n)
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat)
        (WalkLiteralVisit.H position (pos+(n+1)*(N*(2*R)))) (fun _=>1))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralVisit.A rank R L S v code palette work transcript) (fun _=>CompareMachine.word n))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat)
        (WalkLiteralVisit.H position pos) (fun _=>1))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralVisit.A rank R L S v code palette work transcript) (fun _=>CompareMachine.word n)) := by
  let J (i : Nat) := WalkLiteralVisit.H position (pos+(n+1-i)*(N*(2*R)))
  let data := WalkLiteralVisit.A rank R L S v code palette work transcript
  have loop:=PhysicalRepeatStep.run row n (PacketVectorRewind.budget R N) J (fun _=>data) (by
    intro i hi
    have count : n+1-i=n-i+1 := by omega
    have next : n+1-(i+1)=n-i := by omega
    have cursor : pos+(n+1-i)*(N*(2*R))=pos+(n-i)*(N*(2*R))+N*(2*R) := by
      rw [count];ring
    have step:=row_run rank R S L N position (pos+(n-i)*(N*(2*R)))
      v code palette work transcript hRS ready
    simpa only [J,data,cursor,next] using step)
  have last:=(row_run rank R S L N position pos v code palette work transcript hRS ready).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word n)
  have finish : J n=WalkLiteralVisit.H position (pos+N*(2*R)) := by
    simp only [J,Nat.add_sub_cancel_left,Nat.one_mul]
  rw [finish] at loop
  have joined:=loop.seq last
  have start : J 0=WalkLiteralVisit.H position (pos+(n+1)*(N*(2*R))) := by
    simp only [J,Nat.sub_zero]
  have fuel : n*(PacketVectorRewind.budget R N+3)+3+1=
      n*(PacketVectorRewind.budget R N+3)+4 := by omega
  simpa only [machine,budget,data,start,fuel] using joined

end
end Theorem25Completion.WalkTranscriptRewind
