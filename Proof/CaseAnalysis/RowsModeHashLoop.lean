import Proof.CaseAnalysis.RowsModeHashRow

/-! The original prefix depth drives all required Toeplitz rows in order.
The rank-zero/depth-zero case exhausts the actual driver without a row call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashLoop
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding ExtDecompositionBatch CloseoutRowsModeHashReturned CloseoutRowsModeHashRow
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entry (rank C : Nat) (label lower upper translation : List Bool) (row : Nat) (out : List Bool):=
  (⟨CloseoutRowsModeHashRow.machine.start,heads (entryHeads row) out,
    data rank row C label lower upper translation (if row=0 then false else value rank (row-1) label lower upper translation) out⟩ : Configuration 9 _)
noncomputable def machine:=CloseoutRowsDegreeLoop.machine CloseoutRowsModeHashRow.machine
def word (rank depth : Nat) (label lower upper translation : List Bool):=
  (List.range depth).flatMap (fun row=>[value rank row label lower upper translation])
def budget (rank depth : Nat):=depth*(5*rank+22)+3

theorem round_run (rank depth row C : Nat) (label lower upper translation : List Bool) (out : List Bool)
    (hd : depth≤rank) (hr : row<depth) (hC : rank+2≤C) :
    Step CloseoutRowsModeHashRow.machine (5*rank+19)
      (entry rank C label lower upper translation row out).heads (entry rank C label lower upper translation row out).tapes
      (entry rank C label lower upper translation (row+1) (out++[value rank row label lower upper translation])).heads
      (entry rank C label lower upper translation (row+1) (out++[value rank row label lower upper translation])).tapes:=by
  simpa only [entry,show row+1≠0 by omega,if_false,Nat.add_sub_cancel] using
    row_run rank row C label lower upper translation
      (if row=0 then false else value rank (row-1) label lower upper translation) out (by omega) hC

theorem loop_run (rank depth C : Nat) (label lower upper translation : List Bool) (out : List Bool)
    (hd : depth≤rank) (hC : rank+2≤C) :
    ∃ r,runFrom machine (budget rank depth)
      (RepeatMachine.cfg 0 (entry rank C label lower upper translation 0 out) depth 1)=some r ∧
      r.final=RepeatMachine.cfg 3
        (entry rank C label lower upper translation depth (out++word rank depth label lower upper translation)) depth 1 ∧
      r.steps≤budget rank depth:=by
  apply CloseoutRowsDegreeLoop.loop_run CloseoutRowsModeHashRow.machine (entry rank C label lower upper translation)
    (fun row=>[value rank row label lower upper translation]) (5*rank+19) depth (by intro row hr pre;rfl) _ out
  intro row hr pre
  exact round_run rank depth row C label lower upper translation pre hd hr hC

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashLoop
