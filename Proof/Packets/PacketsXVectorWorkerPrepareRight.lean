import Proof.Packets.PacketsXVectorWorkerPrepareLevel

/-! A level provider may physically clear the old right operand. This join
tracks its actual returned right packet while preserving the left packet,
vector banks, and controller scratch layout. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] VectorWorkerArena.windowMachine VectorWorkerArena.deltaTag prepareLevel

theorem prepare_level_right_run {s : Nat} (p : Machine 256 s) (C R ci pi level root old fuel : Nat)
    (left right newRight : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (T : Fin 256→List Bool)
    (hin : ∀j,A C R ci pi level left right [] previous next fields extra (VectorWorkerArena.windowSlots j)=
      GradedWindow.A R root level 0 0 old j)
    (hroot : root+67≤R) (hlevel : level+2≤R) (hold : old+1≤R)
    (htag : (fields 153).length=R)
    (hprovider : Step p fuel providerH (providerA C R left right (levelFields R root level fields)) providerH T)
    (hcore : ∀j : Fin 34,T (j.castAdd 222)=ReusableArithmetic.state C R left newRight j) :
    Step (prepareLevel p) (prepareBudget R root level fuel) (H (fun _=>0))
      (A C R ci pi level left right [] previous next fields extra) (H (fun _=>0))
      (A C R ci pi level left newRight [] previous next (fun j=>T (j.natAdd 34)) extra) := by
  let W:=ZeroPadding.pad R (CompareMachine.word (GradedWindow.window root level))
  let f1:=Function.update fields 118 W
  have first:=VectorWorkerArena.window_run R root level old
    (A C R ci pi level left right [] previous next fields extra) hin hroot hlevel hold
  rw [←heads_eq] at first
  have firstEnd : Function.update (A C R ci pi level left right [] previous next fields extra) 152 W=
      A C R ci pi level left right [] previous next f1 extra :=
    update_meta C R ci pi level left right [] previous next fields extra 118 W
  have first':=first.congr rfl firstEnd
  have middle:=VectorWorkerArena.delta_tag_run R level (A C R ci pi level left right [] previous next f1 extra)
    rfl rfl (by omega) (by change (f1 153).length=R;simpa [f1,Function.update] using htag)
  rw [←heads_eq] at middle
  have midEnd : Function.update (A C R ci pi level left right [] previous next f1 extra) 187
      (ZeroPadding.pad R (CompareMachine.word (level+1)))=
      A C R ci pi level left right [] previous next (levelFields R root level fields) extra :=
    update_meta C R ci pi level left right [] previous next f1 extra 153 _
  have middle':=middle.congr rfl midEnd
  have last:=provider_dock C R ci pi level left right left newRight [] previous next
    (levelFields R root level fields) extra T hprovider hcore
  simpa only [prepareLevel,prepareBudget] using first'.seq (middle'.seq last)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
