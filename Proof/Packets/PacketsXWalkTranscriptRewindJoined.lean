import Proof.Packets.PacketsXWalkTranscriptRewindRun

/-! One ordinary counted walk program writes the exact coordinate transcript
and pays for returning the transcript head to its initial position. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptRewind
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer
open Theorem25Completion.CycleBounds VectorBottomUp
noncomputable section
variable {population active depth n : Nat}

def collectedMachine := Composition.machine WalkLiteralLoop.machine machine
def collectedBudget (C w population active root depth S n : Nat) :=
  WalkLiteralLoop.budget C w population active root depth S n+1+
    budget (commonReserve C w) (population+1) n
attribute [local irreducible] WalkLiteralLoop.machine machine

theorem collected_run (C w d root S L : Nat) (mask : Finset (Fin population)) (wins : Fin depth → Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root S L wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (old : ToeplitzSeed (canonicalGradedRank population active)) (codeTail base tail : List Bool)
    (work : Fin 299 → List Bool) (hw : ∀j,(work j).length≤S) :
    ∃out,Step collectedMachine (collectedBudget C w population active root depth S n)
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat) (WalkLiteralLoop.H C w population n base 0) (fun _=>1))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralLoop.A C w root S L mask wins sample old codeTail base tail 0 work) (fun _=>CompareMachine.word n))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat) (WalkLiteralVisit.H (160*n) base.length) (fun _=>1))
      (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
        (WalkLiteralLoop.A C w root S L mask wins sample old codeTail base tail (n+1) out) (fun _=>CompareMachine.word n)) ∧
      (∀j,(out j).length≤S) ∧ TranscriptRewindReady (commonReserve C w) S (population+1) out := by
  obtain ⟨out,visit,hout,ready⟩:=WalkLiteralLoop.run C w d root S L mask wins h sample old codeTail base tail work hw
  have back:=run (canonicalGradedRank population active) (commonReserve C w) S L (population+1) n
    (160*n) base.length (WalkTimeLoop.vertex sample (n+1))
    (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++codeTail)
    (paddedPalette C (commonReserve C w) population root depth
      (CloseoutRowsModeCache.parameters population active 0 (C+9) mask (WalkLiteralLoop.retainedSeed sample old (n+1)))) out
    (WalkLiteralLoop.transcript (commonReserve C w) (WalkLiteralLoop.stride C w population) (n+1)
      (WalkLiteralLoop.rows C mask wins sample) base tail (n+1))
    (by have hr:=h.reserve;omega) ready
  have heads : WalkLiteralLoop.H C w population n base (n+1)=
      WalkLiteralVisit.H (160*n) (base.length+(n+1)*((population+1)*(2*commonReserve C w))) := by
    simp only [WalkLiteralLoop.H,WalkLiteralLoop.stride,Nat.min_eq_right (by omega : n≤n+1)]
  rw [heads] at visit
  have joined:=visit.seq back
  exact ⟨out,joined,hout,ready⟩

end
end Theorem25Completion.WalkTranscriptRewind
