import Proof.Packets.PacketsXWalkLiteralLoopStep

/-! One fixed ordinary program visits every vertex of a positive walk,
collecting all coordinates in time order. Its count driver is actual input
and is restored; private work is existentially hidden and remains bounded. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer
open Theorem25Completion.CycleBounds VectorBottomUp
noncomputable section
variable {population active depth n : Nat}

def machine := Composition.machine (RepeatMachine.machine body (fun _ _=>true))
  (TapeEmbedding.machine 1 WalkLiteralVisit.machine)
def budget (C w population active root depth S n : Nat) :=
  n*(bodyFuel C w population active root depth S+3)+4+visitFuel C w population active root depth S
attribute [local irreducible] body WalkLiteralVisit.machine

theorem run (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (h : Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (old : ToeplitzSeed (canonicalGradedRank population active)) (codeTail base tail : List Bool)
    (work : Fin 299 → List Bool) (hw : ∀j,(work j).length≤S) :
    ∃out,Step machine (budget C w population active root depth S n)
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat) (H C w population n base 0) (fun _=>1))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (A C w root S L mask wins sample old codeTail base tail 0 work) (fun _=>CompareMachine.word n))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat) (H C w population n base (n+1)) (fun _=>1))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (A C w root S L mask wins sample old codeTail base tail (n+1) out) (fun _=>CompareMachine.word n)) ∧
      (∀j,(out j).length≤S) ∧ TranscriptRewindReady (commonReserve C w) S (population+1) out := by
  let Ready (i : Nat) (a : Fin 332 → List Bool) :=
    ∃work : Fin 299 → List Bool,(∀j,(work j).length≤S) ∧
      a=A C w root S L mask wins sample old codeTail base tail i work
  have start : Ready 0 (A C w root S L mask wins sample old codeTail base tail 0 work) := ⟨work,hw,rfl⟩
  obtain ⟨middle,loop,mid,hmid,he⟩:=PhysicalRepeatExists.run_heads body n
    (bodyFuel C w population active root depth S) (H C w population n base) Ready _ start (by
      intro i hi a ha
      obtain ⟨scratch,hbound,rfl⟩:=ha
      obtain ⟨out,step,hout,_⟩:=iteration C w d root S L mask wins h sample old codeTail base tail i hi scratch hbound
      exact ⟨A C w root S L mask wins sample old codeTail base tail (i+1) out,step,out,hout,rfl⟩)
  subst middle
  obtain ⟨out,last,hout,hready⟩:=final_visit C w d root S L mask wins h sample old codeTail base tail mid hmid
  have finish:=last.embed (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word n)
  have joined:=loop.seq finish
  refine ⟨out,?_,hout,hready⟩
  have fuel : n*(bodyFuel C w population active root depth S+3)+3+1=
      n*(bodyFuel C w population active root depth S+3)+4 := by omega
  simpa only [machine,budget,fuel] using joined

end
end Theorem25Completion.WalkLiteralLoop
