import Proof.Assembly.State

/-! The checked support scan/reset runs on the actual thirteen-port bank.
Only candidate/log false backing is transported by ZeroPadding. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.ResetBank
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open PCJc4297ab269d8423a_Source

def capacity (best : Nat) (i : Fin 10) : Nat := if i.val=4 then best+1 else 0

theorem initial_heads (d : MaskData) (cap offset : Nat) :
    (Reset.initial d.q cap (State.rows d) (State.masks d) offset).heads =
      ![0,offset,offset,offset,1,0,0,1,1,0] := by
  funext i
  fin_cases i <;> simp [Reset.initial,ZeroPadding.config,Rewind.recording,Rewind.config,
    RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Rows.data,Composition.leftConfig,Row.cfg,
    Fin.addCases]

theorem initial_tapes (d : MaskData) (cap offset : Nat) :
    (Reset.initial d.q cap (State.rows d) (State.masks d) offset).tapes =
      ![d.supportWord,[],[],State.double d,CompareMachine.word 0,[false],[false],
        CompareMachine.word d.q,CompareMachine.word d.m,List.replicate cap false] := by
  funext i
  fin_cases i <;> simp [Reset.initial,ZeroPadding.config,ZeroPadding.pad,
    Rewind.Workspace.capacities,Rewind.recording,Rewind.config,RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,Rows.data,Composition.leftConfig,Row.cfg,Fin.addCases,
    State.masks,State.rows_word,CompareMachine.word]

theorem final_heads (d : MaskData) (cap offset : Nat) :
    (Reset.finished d.q cap (State.rows d) (State.masks d) offset).heads =
      ![0,offset,offset,offset,0,0,0,1,1,0] := by
  funext i
  fin_cases i <;> simp [Reset.finished,Reset.finalData,SelectiveReset.finished,Rewind.config,
    RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Rows.data,Composition.leftConfig,
    Row.cfg,Reset.selected,Fin.addCases]

theorem final_tapes (d : MaskData) (cap offset : Nat) :
    (Reset.finished d.q cap (State.rows d) (State.masks d) offset).tapes =
      ![d.supportWord,[],[],State.double d,CompareMachine.word (State.result d offset).1,
        [false],[false],CompareMachine.word d.q,CompareMachine.word d.m,
        List.replicate (max cap (Reset.fuel d.q d.m)) false] := by
  have he : (State.rows d).foldl (Rows.next (State.masks d) offset) (0,false,false) =
      ((State.result d offset).1,false,false) := Prod.ext rfl (State.result_flags d offset)
  simp only [State.masks] at he
  funext i
  fin_cases i <;> simp [Reset.finished,Reset.finalData,SelectiveReset.finished,Rewind.config,
    RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Rows.data,Composition.leftConfig,
    Row.cfg,Fin.addCases,he,State.masks,State.rows_word]


end PCJ93d4cfe17dc847a3.ResetBank
