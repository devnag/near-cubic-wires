import Proof.CaseAnalysis.RowsModeHashSource
import Proof.CaseAnalysis.RowsRawAtomRound

/-! Physical conditional monomial delimiters share the existing original
index copier. A retained bit closes exactly the monomial that was opened. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralMarks
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos j count : Nat) (out : List Bool) : Fin 5→Nat:=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>Nat)
    (RowMaskBodyParts.cfg (0 : Fin 1) [] pos j count out).heads (fun _=>0)
def data (source : List Bool) (j count : Nat) (out : List Bool) (flag : Bool) : Fin 5→List Bool:=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
    (RowMaskBodyParts.cfg (0 : Fin 1) source 0 j count out).tapes (fun _=>[flag])
def cfg {s : Nat} (q : Fin s) (source : List Bool) (pos j count : Nat) (out : List Bool) (flag : Bool) : Configuration 5 s:=
  ⟨q,heads pos j count out,data source j count out flag⟩
def emitted (flag b : Bool) : List Bool:=if flag then [b] else []

def mark (first : Bool) : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q bits=>if q=0 then
    let flag:=if first then bits 0 else bits 4
    some ⟨1,fun i=>if i=4 ∧ first then some (bits 0) else if i=2 ∧ flag then some first else none,
      fun i=>if i=2 ∧ flag then .right else .stay⟩ else none

theorem mark_run (first bit flag : Bool) (source out : List Bool) (pos j count : Nat)
    (hb : readTapeBit source pos=bit) :
    Step (mark first) 1 (heads pos j count out) (data source j count out flag)
      (heads pos j count (out++emitted (if first then bit else flag) first))
      (data source j count (out++emitted (if first then bit else flag) first)
        (if first then bit else flag)):=by
  have hs:step (mark first) (cfg 0 source pos j count out flag)=
      some (cfg 1 source pos j count
        (out++emitted (if first then bit else flag) first) (if first then bit else flag)):=by
    have hb:(cfg (0 : Fin 2) source pos j count out flag).scanned 0=bit:=hb
    have hf:(cfg (0 : Fin 2) source pos j count out flag).scanned 4=flag:=rfl
    simp only [step,mark,hb,hf]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> cases first <;> cases bit <;> cases flag <;>
        simp [applyAction,cfg,heads,emitted,Fin.addCases,RowMaskBodyParts.cfg,HeadMove.apply]
    · funext i;fin_cases i <;> cases first <;> cases bit <;> cases flag <;>
        simp [applyAction,cfg,heads,data,emitted,Fin.addCases,RowMaskBodyParts.cfg,Streaming.write_append,writeTapeBit]
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

noncomputable def emit (b : Bool):=TapeEmbedding.machine 1 (CloseoutRowsRawAtomRound.mark b)

theorem emit_run (b flag : Bool) (source out : List Bool) (pos j count : Nat) :
    Step (emit b) 1 (heads pos j count out) (data source j count out flag)
      (heads pos j count (out++[b])) (data source j count (out++[b]) flag):=by
  obtain ⟨r,hr,rf,_⟩:=CloseoutRowsRawAtomRound.mark_run b source pos j count out
  exact (Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).embed
    (fun _ : Fin 1=>0) (fun _=>[flag])

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralMarks
