import Proof.Packets.PacketVectorRewind
import Proof.Packets.PacketsXWalkLiteralLoopRun

/-! Paid rewind of one row using the words retained by the literal collector. -/
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

def paletteRow := RecoveryFocus.machine collectSlots PacketVectorRewind.machine
def row := PhysicalPrepend.machine 15 paletteRow

theorem palette_row_run (R S N pos : Nat) (palette : Fin 15 → List Bool)
    (work : Fin 299 → List Bool) (transcript : List Bool)
    (hRS : R≤S) (ready : TranscriptRewindReady R S N work) :
    Step paletteRow (PacketVectorRewind.budget R N)
      (collectHeads (pos+N*(2*R))) (collectData palette S work transcript)
      (collectHeads pos) (collectData palette S work transcript) := by
  have pin : ∀j,collectData palette S work transcript (collectSlots j)=
      PacketVectorAppend.paddedTapes R N S (work 257) transcript j := by
    intro j;fin_cases j
    · exact ready.width
    · rfl
    · rfl
    · exact ready.zero
    · exact ready.scratch
    · exact ready.count
  have step:=PacketVectorRewind.padded_run R S N 0 pos (work 257) transcript hRS
  apply PCJ9eff70d512234a4c_Fixed.PhysicalFocusBoundary.focus step collectSlots (by decide)
    (collectHeads (pos+N*(2*R))) (collectHeads pos)
    (collectData palette S work transcript) (collectData palette S work transcript)
  · intro j;fin_cases j <;>rfl
  · exact fun j=>(pin j).symm
  · intro j;fin_cases j <;>rfl
  · exact fun j=>(pin j).symm
  · intro i away
    have ht : i≠316 := by intro he;exact away 2 he.symm
    constructor
    · revert ht
      refine Fin.addCases (m:=316) (n:=1) (fun j=>?_) (fun j=>?_) i
      · intro _;simp only [collectHeads,Fin.addCases_left]
      · fin_cases j;intro ht;exact False.elim (ht rfl)
    · rfl

theorem row_run (rank R S L N position pos : Nat)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool)
    (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) (transcript : List Bool)
    (hRS : R≤S) (ready : TranscriptRewindReady R S N work) :
    Step row (PacketVectorRewind.budget R N)
      (WalkLiteralVisit.H position (pos+N*(2*R)))
      (WalkLiteralVisit.A rank R L S v code palette work transcript)
      (WalkLiteralVisit.H position pos)
      (WalkLiteralVisit.A rank R L S v code palette work transcript) := by
  exact PhysicalPrepend.run (palette_row_run R S N pos palette work transcript hRS ready)
    (WalkSeedResident.heads position) (WalkSeedResident.input rank R L v code)

end
end Theorem25Completion.WalkTranscriptRewind
