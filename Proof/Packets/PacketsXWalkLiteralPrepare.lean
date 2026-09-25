import Proof.Packets.PacketsXWalkLiteralPalette
import Proof.Packets.PhysicalZeroRectangle

/-! Physical preparation of the 333-tape walk arena and its entire transcript.
All 299 vector work tapes and the transcript start empty. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open VectorBottomUp CloseoutRowsModeCache
noncomputable section

def H (position dest : Nat) : Fin 333→Nat :=
  Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat) (WalkLiteralVisit.H position dest) (fun _=>1)
def A (rank R S L n : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool)
    (palette : Fin 15→List Bool) (work : Fin 299→List Bool) (transcript : List Bool) : Fin 333→List Bool :=
  Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
    (WalkLiteralVisit.A rank R L S v code palette work transcript) (fun _=>CompareMachine.word n)
def coldHeads : Fin 333→Nat :=
  Fin.addCases (m:=332) (n:=1) (motive:=fun _=>Nat)
    (Fin.addCases (m:=15) (n:=317) (motive:=fun _=>Nat) (WalkSeedResident.heads 0)
      (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0))) (fun _=>1)
def coldInput (rank R S L n : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (palette : Fin 15→List Bool) : Fin 333→List Bool :=
  Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=15) (n:=317) (motive:=fun _=>List Bool) (WalkSeedResident.input rank R L v code)
      (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>List Bool) (NativeFanout.input (m:=299) palette S) (fun _=>[])))
    (fun _=>CompareMachine.word n)
def bootArena := TapeEmbedding.machine 1 (PhysicalPrepend.machine 15 (TapeEmbedding.machine 1 paletteMachine))

theorem boot_arena_run (C R M root depth S L rank n : Nat) (p : Parameters)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool)
    (h : ColdWordBounds C R M root depth p) (hRS : R+3≤S) (hCS : 2*C+5≤S) :
    Step bootArena (paletteBudget S M) coldHeads
      (coldInput rank R S L n v code (paddedPalette C R M root depth p)) (H 0 0)
      (A rank R S L n v code (paddedPalette C R M root depth p) (work R S (M+1)) []) := by
  have first:=(palette_run C R M root depth S p h hRS hCS).embed
    (fun _ : Fin 1=>0) (fun _ : Fin 1=>[])
  have second:=PhysicalPrepend.run first (WalkSeedResident.heads 0) (WalkSeedResident.input rank R L v code)
  exact second.embed (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word n)

def allocateSlots : Fin 5→Fin 333 := ![61,331,291,327,332]
def allocate := RecoveryFocus.machine allocateSlots PhysicalZeroRectangle.machine

theorem data_update (rank R S L n : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (palette : Fin 15→List Bool) (work : Fin 299→List Bool) (before after : List Bool) :
    Function.update (A rank R S L n v code palette work before) 331 after=
      A rank R S L n v code palette work after := by
  unfold A WalkLiteralVisit.A collectData
  change Function.update (Fin.addCases (m:=332) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=15) (n:=317) (motive:=fun _=>List Bool) (WalkSeedResident.input rank R L v code)
      (Fin.addCases (m:=316) (n:=1) (motive:=fun _=>List Bool) (paletteData palette S work) (fun _=>before)))
    (fun _=>CompareMachine.word n)) ((((0 : Fin 1).natAdd 316).natAdd 15).castAdd 1) after=_
  rw [PhysicalAppendUpdate.left,PhysicalAppendUpdate.right,PhysicalAppendUpdate.right]
  congr 3
  funext i;fin_cases i;rfl

theorem allocate_run (rank R S L N n : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (palette : Fin 15→List Bool) (work : Fin 299→List Bool)
    (ready : TranscriptRewindReady R S N work) :
    Step allocate (PhysicalZeroRectangle.budget R N n) (H 0 0) (A rank R S L n v code palette work [])
      (H 0 0) (A rank R S L n v code palette work (List.replicate ((n+1)*(N*(2*R))) false)) := by
  have pin (bank : List Bool) : ∀j,PhysicalZeroRectangle.paddedTapes R S N n bank j=
      A rank R S L n v code palette work bank (allocateSlots j) := by
    intro j;fin_cases j
    · exact ready.width.symm
    · rfl
    · exact ready.scratch.symm
    · exact ready.count.symm
    · rfl
  apply PhysicalFocusBoundary.focus (PhysicalZeroRectangle.padded_run R S N n) allocateSlots (by decide)
    (H 0 0) (H 0 0) (A rank R S L n v code palette work [])
    (A rank R S L n v code palette work (List.replicate ((n+1)*(N*(2*R))) false))
  · intro j;fin_cases j <;>rfl
  · exact pin []
  · intro j;fin_cases j <;>rfl
  · exact pin _
  · intro i away
    refine ⟨rfl,?_⟩
    have hi : i≠331 := by intro he;exact away 1 he.symm
    have he:=congrFun (data_update rank R S L n v code palette work []
      (List.replicate ((n+1)*(N*(2*R))) false)) i
    simpa only [Function.update_of_ne hi] using he

def prepare := Composition.machine bootArena allocate
def prepareBudget (R S M n : Nat) := paletteBudget S M+1+PhysicalZeroRectangle.budget R (M+1) n

theorem prepare_run (C R M root depth S L rank n : Nat) (p : Parameters)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool)
    (h : ColdWordBounds C R M root depth p) (hRS : R+3≤S) (hCS : 2*C+5≤S) :
    Step prepare (prepareBudget R S M n) coldHeads
      (coldInput rank R S L n v code (paddedPalette C R M root depth p)) (H 0 0)
      (A rank R S L n v code (paddedPalette C R M root depth p) (work R S (M+1))
        (List.replicate ((n+1)*((M+1)*(2*R))) false)) :=
  (boot_arena_run C R M root depth S L rank n p v code h hRS hCS).seq
    (allocate_run rank R S L (M+1) n v code _ _ (work_ready R S (M+1)))

end
end Theorem25Completion.WalkLiteralCold
