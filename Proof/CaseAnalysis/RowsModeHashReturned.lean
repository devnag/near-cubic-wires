import Proof.CaseAnalysis.RowsModeHashMeaning

/-! Return the three forward-scanned heads after one actual Toeplitz bit.
The original seed words are retained, and the translation cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashReturned
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsModeHashBit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 7):=decide (i=0∨i=1∨i=3)
def machine:=MaskedReset.machine CloseoutRowsModeHashBit.machine selected
def entryHeads (row : Nat) : Fin 8→Nat:=![0,0,row,0,row,row,0,0]
def finalHeads (row : Nat) : Fin 8→Nat:=![0,0,0,0,0,row,0,0]
def data (rank row C : Nat) (label lower upper translation : List Bool) (acc : Bool) : Fin 8→List Bool:=
  Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
    (CloseoutRowsModeHashBit.data rank row label lower upper translation acc) (fun _=>List.replicate C false)
def value (rank row : Nat) (label lower upper translation : List Bool):=
  fold row label lower upper (List.range rank) (readTapeBit translation row)

theorem returned_run (rank row C : Nat) (label lower upper translation : List Bool) (old : Bool)
    (hr : row<rank) (hC : rank+2≤C) :
    Step machine (2*rank+6) (entryHeads row) (data rank row C label lower upper translation old)
      (finalHeads row) (data rank row C label lower upper translation (value rank row label lower upper translation)):=by
  obtain ⟨base,hb,bf,_⟩:=hash_run rank row label lower upper translation old hr
  have raw:=(Step.of_run hb (congrArg Configuration.heads bf) (congrArg Configuration.tapes bf)).mask selected
    (by intro i hi;fin_cases i <;> simp_all [selected,heads]) hC
  have time:2*(rank+2)+2=2*rank+6:=by omega
  rw [time] at raw
  apply (raw.congr_in ?_ rfl).congr ?_ rfl
  · funext i;fin_cases i <;> simp [heads,entryHeads,Fin.addCases]
  · funext i;fin_cases i <;> simp [cfg,heads,selected,finalHeads,Fin.addCases,show row-rank=0 by omega]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashReturned
