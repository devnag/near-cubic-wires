import Proof.Packets.PacketsXVectorLiteralPaletteBoot

/-! Paid full-arena erasure and restoration from retained input masters. -/
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

def paletteEraseSlots (j : Fin 301) : Fin 316 := j.natAdd 15
theorem palette_erase_injective : Function.Injective paletteEraseSlots := by
  intro i j he
  apply Fin.ext
  have hv:=congrArg (fun z : Fin 316=>z.val) he
  dsimp only [paletteEraseSlots,Fin.val_natAdd] at hv
  omega
def paletteErase := RecoveryFocus.machine paletteEraseSlots (RecoveryScratchErase.resetMachine 299)
def paletteReset := Composition.machine paletteLower paletteErase

theorem palette_erase_run (palette : Fin 15 → List Bool) (S : Nat)
    (work : Fin 299 → List Bool) (hwork : ∀i,(work i).length ≤ S) :
    Step paletteErase (2*S+4) (fun _=>0) (paletteData palette S work)
      (fun _=>0) (paletteData palette S (fun _=>List.replicate S false)) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready S (S+1) work hwork)
  simp only [max_self] at h
  apply PhysicalFocusBoundary.focus h paletteEraseSlots palette_erase_injective
    (fun _=>0) (fun _=>0) (paletteData palette S work)
    (paletteData palette S (fun _=>List.replicate S false))
  · intro i;rfl
  · intro i
    refine Fin.addCases (m:=299) (n:=2) (fun j=>?_) (fun j=>?_) i
    · have hj : (j.castAdd 2 : Fin 301)=(j.castAdd 1).castAdd 1 := rfl
      simp only [paletteEraseSlots,hj,Fin.addCases_left]
      exact (palette_arena_data palette S work j).symm
    · fin_cases j <;>rfl
  · intro i;rfl
  · intro i
    refine Fin.addCases (m:=299) (n:=2) (fun j=>?_) (fun j=>?_) i
    · have hj : (j.castAdd 2 : Fin 301)=(j.castAdd 1).castAdd 1 := rfl
      simp only [paletteEraseSlots,hj,Fin.addCases_left]
      exact (palette_arena_data palette S (fun _=>List.replicate S false) j).symm
    · fin_cases j <;>rfl
  · intro i
    refine Fin.addCases (m:=315) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=15) (n:=300) (fun k=>?_) (fun k=>?_) j
      · intro _;constructor <;>simp only [paletteData,Fin.addCases_left,Fin.addCases_right]
      · refine Fin.addCases (m:=299) (n:=1) (fun l=>?_) (fun l=>?_) k
        · intro away
          exact False.elim (away (l.castAdd 2) (by apply Fin.ext;rfl))
        · intro away;fin_cases l
          exact False.elim (away 299 rfl)
    · intro away;fin_cases j
      exact False.elim (away 300 rfl)

theorem palette_reset_run (palette : Fin 15 → List Bool) (S : Nat)
    (work : Fin 299 → List Bool) (hwork : ∀i,(work i).length ≤ S) :
    Step paletteReset (2*S+6) (paletteHeads VectorNumericArena.heads) (paletteData palette S work)
      (fun _=>0) (paletteData palette S (fun _=>List.replicate S false)) := by
  have run:=(palette_lower_run (paletteData palette S work)).seq (palette_erase_run palette S work hwork)
  simpa only [paletteReset,show 1+1+(2*S+4)=2*S+6 by omega] using run

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
