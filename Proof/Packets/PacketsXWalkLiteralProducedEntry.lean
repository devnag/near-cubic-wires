import Proof.Packets.PacketsXWalkLiteralProducedPrepare
import Proof.Packets.PacketsXWalkLiteralProducedMasters

/-! The physically prepared boundary is obtained from the actual graded master
outputs. Every copy is an ordinary run and every new tape starts empty. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section
attribute [local irreducible] WalkLiteralMasters.gradedMachine

attribute [local irreducible] mastersMachine prepareMachine

theorem retained_entry_run (C R root population active S n : Nat) (mask x y code : List Bool)
    (h : WalkLiteralMasters.Bounds C R root (SourceGradedRank.rank population active)
      (SourceGradedRank.depth active) population mask) (hx : x.length≤R) (hy : y.length≤R) :
    ∃masters,Step entryMachine (entryBudget C R root population active mask)
      (fun _=>0) (input C R root population active S n mask x y code)
      preparedHeads (prepared masters (SourceGradedRank.rank population active) R S n x y code) ∧
      (∀i,masters (paletteSlots i)=WalkLiteralMasters.palette C R root (SourceGradedRank.rank population active)
        (SourceGradedRank.depth active) population mask i) ∧ Retained C R root population active mask masters := by
  obtain ⟨masters,first,hp,retained⟩:=graded_retained_run C R root population active mask h
  have pins : ∀i,masters (paletteSlots i)=WalkLiteralMasters.palette C R root (SourceGradedRank.rank population active)
      (SourceGradedRank.depth active) population mask i := by intro i;rw [palette_slots_original];exact hp i
  have boot:=first.embed (fun _ : Fin 338=>0) (extras S n x y code)
  have zeros : Fin.addCases (m:=95) (n:=338) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)=(fun _=>0) := by
    funext i
    refine Fin.addCases (m:=95) (n:=338) (fun j=>?_) (fun j=>?_) i <;>
      simp only [Fin.addCases_left,Fin.addCases_right]
  rw [zeros] at boot
  have prep:=prepare_run C R root (SourceGradedRank.rank population active) (SourceGradedRank.depth active)
    population S n mask x y code masters pins h.rank hx hy
  refine ⟨masters,?_,pins,retained⟩
  simpa only [entryMachine,mastersMachine,entryBudget,input,bank0] using boot.seq prep


end
end Theorem25Completion.WalkLiteralProduced
