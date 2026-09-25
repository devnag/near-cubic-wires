import Proof.CaseAnalysis.RowsModeHashPosition

/-! The next Toeplitz row derives its cursor positions from its own
incremented unary template, retaining the same original seed tapes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashPrepare
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch CloseoutRowsModeHashReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowSlot : Fin 1→Fin 8:=fun _=>4
def positionSlots : Fin 3→Fin 8:=![4,2,5]
noncomputable def advance:=RecoveryFocus.machine rowSlot CloseoutRowsDegreeAdvance.templateMachine
noncomputable def position:=RecoveryFocus.machine positionSlots CloseoutRowsModeHashPosition.machine
noncomputable def machine:=Composition.machine advance position

theorem advance_run (rank row C : Nat) (label lower upper translation : List Bool) (acc : Bool) :
    Step advance (2*row+6) (finalHeads row) (data rank row C label lower upper translation acc)
      (finalHeads row) (data rank (row+1) C label lower upper translation acc):=by
  have raw:=(Step.of_ready (CloseoutRowsDegreeAdvance.template_ready row)).dock rowSlot (by decide)
    (finalHeads row) (data rank row C label lower upper translation acc) (by intro i;rfl) (by intro i;rfl)
  apply raw.congr
  · exact dockH_existing rowSlot _ _ (by intro i;rfl)
  · apply HierarchyAllocation.install_eq rowSlot (by decide)
    · intro i;rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)

theorem position_run (rank row C : Nat) (label lower upper translation : List Bool) (acc : Bool) :
    Step position (row+3) (finalHeads row) (data rank (row+1) C label lower upper translation acc)
      (entryHeads (row+1)) (data rank (row+1) C label lower upper translation acc):=by
  have raw:=(CloseoutRowsModeHashPosition.position_run (row+1) row lower translation).dock positionSlots (by decide)
    (finalHeads row) (data rank (row+1) C label lower upper translation acc)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  have time:row+1+2=row+3:=by omega
  rw [time] at raw
  apply raw.congr
  · funext i;fin_cases i
    all_goals first
      | exact dockH_slot positionSlots (by decide) _ _ 0
      | exact dockH_slot positionSlots (by decide) _ _ 1
      | exact dockH_slot positionSlots (by decide) _ _ 2
      | exact dockH_other positionSlots _ _ _ (by intro i;fin_cases i <;> decide)
  · exact install_existing positionSlots _ _ (by intro i;fin_cases i <;> rfl)

theorem prepare_run (rank row C : Nat) (label lower upper translation : List Bool) (acc : Bool) :
    Step machine (3*row+10) (finalHeads row) (data rank row C label lower upper translation acc)
      (entryHeads (row+1)) (data rank (row+1) C label lower upper translation acc):=by
  have raw:=(advance_run rank row C label lower upper translation acc).seq (position_run rank row C label lower upper translation acc)
  have time:2*row+6+1+(row+3)=3*row+10:=by omega
  rw [time] at raw
  exact raw

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashPrepare
