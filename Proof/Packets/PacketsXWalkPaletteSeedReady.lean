import Proof.Packets.PacketsXWalkPaletteSeedCopy
import Proof.Packets.PacketsXWalkSeedCleanup
import Proof.Packets.PacketsXVectorLiteralPaletteUpdate

/-! Decode an actual walk vertex, copy its three seed words into retained
palette masters, and clear the decoder for the next visit. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 18000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkPaletteSeedReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
noncomputable section

def H (position : Nat) (work : Fin 299 → Nat) : Fin 331 → Nat :=
  Fin.addCases (m:=15) (n:=316) (motive:=fun _=>Nat)
    (WalkSeedResident.heads position) (paletteHeads work)
def A (rank R L S : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) : Fin 331 → List Bool :=
  Fin.addCases (m:=15) (n:=316) (motive:=fun _=>List Bool)
    (WalkSeedResident.input rank R L v code) (paletteData palette S work)
def middle (rank R L S : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code a b : List Bool) (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) : Fin 331 → List Bool :=
  Fin.addCases (m:=15) (n:=316) (motive:=fun _=>List Bool)
    (WalkSeedResident.output rank R L v code a b) (paletteData palette S work)
def machine := Composition.machine (TapeEmbedding.machine 316 WalkSeedResident.machine)
  (Composition.machine WalkPaletteSeedCopy.machine (TapeEmbedding.machine 316 WalkSeedCleanup.machine))
def budget (rank R : Nat) := 28*rank+8*R+61

theorem middle_source (rank R L S : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code a b : List Bool) (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) (j : Fin 3) :
    middle rank R L S v code a b palette work (WalkPaletteSeedCopy.source j)=
      ZeroPadding.pad R (WalkSeedResident.fields rank v j) := by
  have h:=WalkPaletteSeedCopy.resident_target rank R L v code a b (paletteData palette S work) j
  rw [WalkPaletteSeedCopy.target_word] at h
  exact h

theorem copy_output (rank R L S : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code a b : List Bool) (palette : Fin 15 → List Bool) (work : Fin 299 → List Bool) :
    WalkPaletteSeedCopy.output (middle rank R L S v code a b palette work) =
      middle rank R L S v code a b (seedPalette R palette (WalkSeedResident.fields rank v)) work := by
  have h0:=middle_source rank R L S v code a b palette work 0
  have h1:=middle_source rank R L S v code a b palette work 1
  have h2:=middle_source rank R L S v code a b palette work 2
  change middle rank R L S v code a b palette work 11=_ at h0
  change middle rank R L S v code a b palette work 12=_ at h1
  change middle rank R L S v code a b palette work 13=_ at h2
  unfold WalkPaletteSeedCopy.output
  rw [h0,h1,h2]
  unfold middle
  change Function.update (Function.update (Function.update
    (Fin.addCases (m:=15) (n:=316) (motive:=fun _=>List Bool)
      (WalkSeedResident.output rank R L v code a b) (paletteData palette S work))
    (((6 : Fin 15).castAdd 301).natAdd 15) (ZeroPadding.pad R (WalkSeedResident.fields rank v 0)))
    (((7 : Fin 15).castAdd 301).natAdd 15) (ZeroPadding.pad R (WalkSeedResident.fields rank v 1)))
    (((8 : Fin 15).castAdd 301).natAdd 15) (ZeroPadding.pad R (WalkSeedResident.fields rank v 2))=_
  rw [walk_palette_update_master _ _ _ _ 6,
    walk_palette_update_master _ _ _ _ 7,walk_palette_update_master _ _ _ _ 8]
  rfl

theorem run (rank R L S position : Nat) (hr : 0<rank) (hR : 8*rank+14 ≤ R)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool)
    (palette : Fin 15 → List Bool) (workHeads : Fin 299 → Nat) (work : Fin 299 → List Bool)
    (hw : palette 2=UnaryTemplate.tape R)
    (ht : ∀j : Fin 3,(palette ⟨6+j.val,by omega⟩).length=R) :
    Step machine (budget rank R) (H position workHeads) (A rank R L S v code palette work)
      (H position workHeads)
      (A rank R L S v code (seedPalette R palette (WalkSeedResident.fields rank v)) work) := by
  obtain ⟨a,b,decode,ha,hb⟩:=WalkSeedResident.run rank R L position hr v code
  have first:=decode.embed (paletteHeads workHeads) (paletteData palette S work)
  have fieldfit : ∀j,(WalkSeedResident.fields rank v j).length ≤ R := by
    intro j;fin_cases j <;>simp [WalkSeedResident.fields] <;>omega
  have copy:=WalkPaletteSeedCopy.run R (H position workHeads)
    (middle rank R L S v code a b palette work)
    (by intro j;fin_cases j <;>rfl) hw
    (by
      intro j
      rw [middle_source,ZeroPadding.pad_length,Nat.max_eq_left (fieldfit j)])
    (by
      intro j;fin_cases j
      · exact ht 0
      · exact ht 1
      · exact ht 2)
  rw [copy_output] at copy
  have last:=(WalkSeedCleanup.run rank R L position v code a b hR ha hb).embed
    (paletteHeads workHeads) (paletteData (seedPalette R palette (WalkSeedResident.fields rank v)) S work)
  have all:=first.seq (copy.seq last)
  simpa only [machine,budget,H,A,
    show (28*rank+43)+1+((6*R+12)+1+(2*R+4))=28*rank+8*R+61 by omega] using all

end
end Theorem25Completion.WalkPaletteSeedReady
