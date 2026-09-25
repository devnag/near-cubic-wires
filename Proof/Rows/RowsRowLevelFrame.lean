import Proof.Rows.RowsRowLevelStream

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsRowLevel
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairSource.ProjectionNormalization
noncomputable section

/-- **C6, framed placement.** Port assignment `u`: `u 0` the word, `u 1` its unary length driver,
`u 2` the output (a cleared payload port), `u 3` a blank log. -/
theorem frame_step {T : Nat} (u : Fin 4 → Fin T) (hu : Function.Injective u)
    (w : List Bool) (K S r0 r1 : Nat) (hS : 2*w.length+1 ≤ S)
    (H : Fin T → Nat) (A : Fin T → List Bool) (hH : ∀ i,H (u i)=0)
    (a0 : A (u 0)=ZeroPadding.pad r0 w) (a1 : A (u 1)=ZeroPadding.pad r1 (List.replicate w.length true))
    (a2 : A (u 2)=List.replicate K false) (a3 : A (u 3)=List.replicate S false) :
    Step (RecoveryFocus.machine u RawFrame.machine) (4*w.length+4) H A H
      (Function.update A (u 2) (ZeroPadding.pad K (frame w))) := by
  classical
  let cap : Fin 4 → Nat := ![r0,r1,K,S]
  obtain ⟨r,run,tapes,hs,_⟩ := RawFrame.ready w
  have base := (Step.of_run run (funext hs) tapes).pad cap
  have docked := base.dock u hu H A hH (by
    intro i
    fin_cases i
    · exact a0
    · exact a1
    · show A (u 2)=ZeroPadding.pad K []
      rw [a2,padNil]
    · show A (u 3)=ZeroPadding.pad S []
      rw [a3,padNil])
  refine docked.congr (dockH_existing _ _ _ hH) ?_
  funext x
  by_cases hx2 : x=u 2
  · subst hx2
    rw [Function.update_self,install_slot _ hu]
    rfl
  · rw [Function.update_of_ne hx2]
    by_cases hux : ∃ i,u i=x
    · obtain ⟨i,rfl⟩ := hux
      rw [install_slot _ hu]
      fin_cases i
      · show ZeroPadding.pad r0 w=A (u 0)
        rw [a0]
      · show ZeroPadding.pad r1 (List.replicate w.length true)=A (u 1)
        rw [a1]
      · exact absurd rfl hx2
      · show ZeroPadding.pad S (List.replicate (2*w.length+1) false)=A (u 3)
        rw [a3,pad_replicate_false _ _ hS]
    · exact install_other _ _ _ _ (fun i he=>hux ⟨i,he⟩)

/-- Field 8 of the datum is the selection mask (warm field 2): the word C6 places for C3. -/
theorem mask_field (d : P1TopDownPaidReusable.Datum) :
    fieldWord d 8=CompetitorCountMask.mask
      (CompetitorSelectedCells.cells d.row.odd (fun _ _=>0) d.select) := rfl


end
end RowsRowLevel
