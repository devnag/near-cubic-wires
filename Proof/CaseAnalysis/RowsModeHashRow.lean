import Proof.CaseAnalysis.RowsModeHashPrepare

/-! One complete physical hash row returns its scans, appends the computed
bit, and positions the original seed for the next row. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashRow
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsModeHashReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (H : Fin 8→Nat) (out : List Bool) : Fin 9→Nat:=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>Nat) H (fun _=>out.length)
def data (rank row C : Nat) (label lower upper translation : List Bool) (acc : Bool) (out : List Bool) : Fin 9→List Bool:=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
    (CloseoutRowsModeHashReturned.data rank row C label lower upper translation acc) (fun _=>out)
def append : Machine 9 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q bits=>if q=0 then some ⟨1,fun i=>if i=8 then some (bits 6) else none,
    fun i=>if i=8 then .right else .stay⟩ else none
noncomputable def first:=Composition.machine (TapeEmbedding.machine 1 CloseoutRowsModeHashReturned.machine) append
noncomputable def machine:=Composition.machine first (TapeEmbedding.machine 1 CloseoutRowsModeHashPrepare.machine)

theorem append_run (rank row C : Nat) (label lower upper translation : List Bool) (acc : Bool) (out : List Bool) :
    Step append 1 (heads (finalHeads row) out) (data rank row C label lower upper translation acc out)
      (heads (finalHeads row) (out++[acc])) (data rank row C label lower upper translation acc (out++[acc])):=by
  have hs:step append ⟨0,heads (finalHeads row) out,data rank row C label lower upper translation acc out⟩=
      some ⟨1,heads (finalHeads row) (out++[acc]),data rank row C label lower upper translation acc (out++[acc])⟩:=by
    have hread:(⟨0,heads (finalHeads row) out,data rank row C label lower upper translation acc out⟩ : Configuration 9 2).scanned 6=acc:=rfl
    simp only [step,append,if_true,hread]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,heads,HeadMove.apply,Fin.addCases]
    · funext i;fin_cases i <;> simp [applyAction,heads,data,Streaming.write_append,Fin.addCases]
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem row_run (rank row C : Nat) (label lower upper translation : List Bool) (old : Bool) (out : List Bool)
    (hr : row<rank) (hC : rank+2≤C) :
    Step machine (5*rank+19) (heads (entryHeads row) out) (data rank row C label lower upper translation old out)
      (heads (entryHeads (row+1)) (out++[value rank row label lower upper translation]))
      (data rank (row+1) C label lower upper translation (value rank row label lower upper translation)
        (out++[value rank row label lower upper translation])):=by
  have a:=(returned_run rank row C label lower upper translation old hr hC).embed (fun _ : Fin 1=>out.length) (fun _=>out)
  have b:=append_run rank row C label lower upper translation (value rank row label lower upper translation) out
  have c:=(CloseoutRowsModeHashPrepare.prepare_run rank row C label lower upper translation
    (value rank row label lower upper translation)).embed
    (fun _ : Fin 1=>(out++[value rank row label lower upper translation]).length)
    (fun _=>out++[value rank row label lower upper translation])
  have raw:=(a.seq b).seq c
  exact raw.enlarge (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashRow
