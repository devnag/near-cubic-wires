import Proof.CaseAnalysis.RowsModeLiteralSelect

/-! Exact retained hash fields at the enclosing cache boundary. Only the
row template, accumulator and hash bitmap require physical clearing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashFields
open LocalBitMultitape RepairSource.VerifierDecoding CloseoutRowsModeHashReady
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def before (rank depth C : Nat) (label lower upper translation : List Bool) : Fin 11→List Bool:=
  ![List.replicate rank true,label,lower,upper,List.replicate C false,translation,List.replicate C false,
    List.replicate C false,List.replicate C false,CompareMachine.word depth,List.replicate C false]
def accumulator (rank depth : Nat) (label lower upper translation : List Bool):=
  if depth=0 then false else CloseoutRowsModeHashReturned.value rank (depth-1) label lower upper translation
def after (rank depth C : Nat) (label lower upper translation : List Bool) : Fin 11→List Bool:=
  ![List.replicate rank true,label,lower,upper,ZeroPadding.pad C (CompareMachine.word depth),translation,
    ZeroPadding.pad C [accumulator rank depth label lower upper translation],List.replicate C false,
    ZeroPadding.pad C (CloseoutRowsModeHashLoop.word rank depth label lower upper translation),
    CompareMachine.word depth,List.replicate C false]

theorem input_eq (rank depth C : Nat) (label lower upper translation : List Bool) (hC : 1≤C) :
    input rank depth C label lower upper translation=before rank depth C label lower upper translation:=by
  have hz:ZeroPadding.pad C [false]=List.replicate C false:=by
    simpa only [List.replicate_one,max_eq_left hC] using Rewind.Workspace.pad_zeros C 1
  have he:ZeroPadding.pad C []=List.replicate C false:=by simp [ZeroPadding.pad]
  funext i;fin_cases i <;>
    simp [input,before,caps,CloseoutRowsModeHashSource.source,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      CloseoutRowsModeHashLoop.entry,CloseoutRowsModeHashRow.data,CloseoutRowsModeHashReturned.data,
      CloseoutRowsModeHashBit.data,Fin.addCases,CompareMachine.word,hz,Rewind.Workspace.pad_zeros,he]

theorem output_eq (rank depth C : Nat) (label lower upper translation : List Bool) :
    output rank depth C label lower upper translation=after rank depth C label lower upper translation:=by
  funext i;fin_cases i <;>
    simp [output,after,caps,final,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      CloseoutRowsModeHashLoop.entry,CloseoutRowsModeHashRow.data,CloseoutRowsModeHashReturned.data,
      CloseoutRowsModeHashBit.data,Fin.addCases,accumulator]

theorem word_length (rank depth : Nat) (label lower upper translation : List Bool) :
    (CloseoutRowsModeHashLoop.word rank depth label lower upper translation).length=depth:=by
  unfold CloseoutRowsModeHashLoop.word
  rw [←List.map_eq_flatMap]
  simp

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashFields
