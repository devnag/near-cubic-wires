import Proof.Packets.PacketsXVectorLiteralPalette

/-! Actual fifteen-word fanout and paid positioning of the seven arena
cursors. All 299 destination tapes may be empty at entry. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding CloseoutRowsModeCache
noncomputable section

def paletteData (palette : Fin 15 → List Bool) (S : Nat) (work : Fin 299 → List Bool) : Fin 316 → List Bool :=
  Fin.addCases (m:=315) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=15) (n:=300) (motive:=fun _=>List Bool) palette
      (Fin.addCases (m:=299) (n:=1) (motive:=fun _=>List Bool) work (fun _=>List.replicate S true)))
    (fun _=>List.replicate (S+1) false)

def paletteHeads (work : Fin 299 → Nat) : Fin 316 → Nat :=
  Fin.addCases (m:=315) (n:=1) (motive:=fun _=>Nat)
    (Fin.addCases (m:=15) (n:=300) (motive:=fun _=>Nat) (fun _=>0)
      (Fin.addCases (m:=299) (n:=1) (motive:=fun _=>Nat) work (fun _=>0))) (fun _=>0)

def paletteArenaSlots (i : Fin 299) : Fin 316 := (i.natAdd 15).castAdd 2
def paletteHeadSlots : Fin 7 → Fin 316 := ![46,273,274,275,311,312,313]
def paletteRaise := RecoveryFocus.machine paletteHeadSlots (Completion.PhysicalDriverMoves.machine 7 .right)
def paletteLower := RecoveryFocus.machine paletteHeadSlots (Completion.PhysicalDriverMoves.machine 7 .left)
def coldPaletteBoot := Composition.machine (NativeFanout.machine coldSelect) paletteRaise

theorem palette_arena_injective : Function.Injective paletteArenaSlots := by
  intro i j he
  apply Fin.ext
  have h:=congrArg (fun x : Fin 316=>x.val) he
  dsimp only [paletteArenaSlots,Fin.val_castAdd,Fin.val_natAdd] at h
  omega

theorem palette_arena_data (palette : Fin 15 → List Bool) (S : Nat)
    (work : Fin 299 → List Bool) (i : Fin 299) :
    paletteData palette S work (paletteArenaSlots i)=work i := by
  change paletteData palette S work (((i.castAdd 1).natAdd 15).castAdd 1)=work i
  simp only [paletteData,Fin.addCases_left,Fin.addCases_right]

theorem palette_arena_heads (work : Fin 299 → Nat) (i : Fin 299) :
    paletteHeads work (paletteArenaSlots i)=work i := by
  change paletteHeads work (((i.castAdd 1).natAdd 15).castAdd 1)=work i
  simp only [paletteHeads,Fin.addCases_left,Fin.addCases_right]

theorem palette_raise_run (A : Fin 316 → List Bool) :
    Step paletteRaise 1 (fun _=>0) A (paletteHeads VectorNumericArena.heads) A := by
  have h:=Completion.PhysicalDriverMoves.run .right (fun _ : Fin 7=>0) (fun i=>A (paletteHeadSlots i))
  apply PhysicalFocusBoundary.focus h paletteHeadSlots (by decide)
    (fun _=>0) (paletteHeads VectorNumericArena.heads) A A
  · intro i;rfl
  · intro i;rfl
  · intro i
    have all : ∀i,paletteHeads VectorNumericArena.heads (paletteHeadSlots i)=1 := by decide
    exact (all i).symm
  · intro i;rfl
  · intro i away
    have all : ∀i : Fin 316,paletteHeads VectorNumericArena.heads i=0 ∨ ∃j,paletteHeadSlots j=i := by decide
    rcases all i with hz|⟨j,hj⟩
    · exact ⟨hz.symm,rfl⟩
    · exact False.elim (away j hj)

theorem palette_lower_run (A : Fin 316 → List Bool) :
    Step paletteLower 1 (paletteHeads VectorNumericArena.heads) A (fun _=>0) A := by
  have h:=Completion.PhysicalDriverMoves.run .left (fun _ : Fin 7=>1) (fun i=>A (paletteHeadSlots i))
  apply PhysicalFocusBoundary.focus h paletteHeadSlots (by decide)
    (paletteHeads VectorNumericArena.heads) (fun _=>0) A A
  · intro i
    have all : ∀i,paletteHeads VectorNumericArena.heads (paletteHeadSlots i)=1 := by decide
    exact (all i).symm
  · intro i;rfl
  · intro i;rfl
  · intro i;rfl
  · intro i away
    have all : ∀i : Fin 316,paletteHeads VectorNumericArena.heads i=0 ∨ ∃j,paletteHeadSlots j=i := by decide
    rcases all i with hz|⟨j,hj⟩
    · exact ⟨hz,rfl⟩
    · exact False.elim (away j hj)

theorem cold_palette_output (C R M root depth S : Nat) (p : Parameters)
    (hRS : R+3 ≤ S) :
    NativeFanout.output coldSelect (coldPalette C R M root depth p) S =
      paletteData (coldPalette C R M root depth p) S
        (fun i=>ZeroPadding.pad S (coldData C R (coldFields C R M root depth p) (coldExtra R) i)) := by
  have he:=cold_palette_data C R M root depth S p hRS
  change paletteData (coldPalette C R M root depth p) S
    (fun i=>ZeroPadding.pad S (NativeFanout.word coldSelect (coldPalette C R M root depth p) i))=_
  rw [he]

theorem cold_palette_boot_run (C R M root depth S : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) (hRS : R+3 ≤ S) (hCS : 2*C+5 ≤ S) :
    Step coldPaletteBoot (2*S+6) (fun _=>0)
      (NativeFanout.input (m:=299) (coldPalette C R M root depth p) S)
      (paletteHeads VectorNumericArena.heads)
      (paletteData (coldPalette C R M root depth p) S
        (fun i=>ZeroPadding.pad S (coldData C R (coldFields C R M root depth p) (coldExtra R) i))) := by
  have fanout:=Step.of_ready (NativeFanout.ready coldSelect (coldPalette C R M root depth p) S
    (cold_palette_length C R M root depth S p h hRS hCS))
  rw [cold_palette_output C R M root depth S p hRS] at fanout
  have run:=fanout.seq (palette_raise_run _)
  simpa only [coldPaletteBoot,show 2*S+4+1+1=2*S+6 by omega] using run

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
