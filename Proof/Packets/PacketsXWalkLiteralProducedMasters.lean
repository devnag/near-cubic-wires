import Proof.Packets.PacketsXWalkLiteralMastersFrame
import Proof.Packets.PacketsXWalkLiteralProducedData

/-! The palette's rank and depth are actual outputs of the original graded
rank computation. Entry supplies population and active count, no rank/depth words. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed.Materializer
open Completion
open Theorem25Completion.WalkLiteralMasters
noncomputable section
attribute [local irreducible] WalkLiteralMasters.machine SourceGradedRank.machine

structure Retained (C R root population active : Nat) (mask : List Bool) (A : Fin 95→List Bool) : Prop where
  Cword : A 40=List.replicate C true
  Rword : A 41=List.replicate R true
  rootword : A 42=List.replicate root true
  populationword : A 11=List.replicate population true
  activeword : A 0=List.replicate active true
  maskword : A 46=mask

theorem graded_retained_run (C R root population active : Nat) (mask : List Bool)
    (h : Bounds C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active) population mask) :
    ∃out,Step gradedMachine (gradedBudget C R root population active mask)
      (fun _=>0) (gradedInput C R root population active mask) (fun _=>0) out ∧
      (∀i,out (gradedSlots (WalkLiteralMasters.paletteSlots i))=
        palette C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active) population mask i) ∧
      Retained C R root population active mask out := by
  obtain ⟨rankData,rankRun,hr,_hcount,hd,_hdcount,hp,_ha⟩:=SourceGradedRank.run population active
  let middle : Fin 95→List Bool:=Fin.addCases (m:=40) (n:=55) (motive:=fun _=>List Bool)
    rankData (gradedExtra C R root mask)
  have first:=rankRun.embed (fun _ : Fin 55=>0) (gradedExtra C R root mask)
  have zeros : Fin.addCases (m:=40) (n:=55) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    refine Fin.addCases (m:=40) (n:=55) (fun j=>?_) (fun j=>?_) i <;>
      simp only [Fin.addCases_left,Fin.addCases_right]
  rw [zeros] at first
  have localRun:=run C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active) population mask h
  have second:=localRun.focus gradedSlots graded_slots_injective (fun _=>0) middle
  have dock : dockH gradedSlots (fun _ : Fin 95=>0) (fun _=>0)=(fun _=>0) := by
    funext i;unfold dockH;cases RecoveryFocus.pick gradedSlots i <;>rfl
  have pins:=graded_join C R root population active mask rankData hr hd hp
  have finalStep:=(second.congr_in dock (install_existing _ _ _ pins)).congr dock rfl
  have joined:=first.seq finalStep
  refine ⟨_,joined,?_,?_⟩
  · intro i
    exact (install_slot gradedSlots graded_slots_injective middle _ (WalkLiteralMasters.paletteSlots i)).trans
      (palette_output C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active) population mask h i)

  · have retained (i : Fin 7) : install gradedSlots middle
        (bank10 C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active) population mask)
        (gradedSlots (i.castAdd 48)) =
        WalkLiteralMasters.input C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active) population mask (i.castAdd 48) := by
      rw [install_slot gradedSlots graded_slots_injective]
      exact source_retained _ _ _ _ _ _ _ i
    refine ⟨retained 0,retained 1,retained 2,retained 5,?_,retained 6⟩
    rw [install_other gradedSlots _ _ 0]
    · exact _ha
    · intro j
      unfold gradedSlots
      split_ifs <;>try decide
      intro he
      have hv:=congrArg Fin.val he
      dsimp at hv
      omega

end
end Theorem25Completion.WalkLiteralProduced
