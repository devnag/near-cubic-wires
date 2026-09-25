import Proof.CaseAnalysis.RowsModeLiteralPrefix
import Proof.CaseAnalysis.RowsRawPairSeek

/-! One actual literal-cache pair. Both scalar flags are physically read;
the original unary index advances even for an empty variable polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralPair
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsModeLiteralMarks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pair (neg bit : Bool) (index : Nat) : CloseoutRowsRawPairSeek.Pair:=
  (if neg then [[]] else [],if bit then [[index]] else [])
noncomputable def a:=Composition.machine CloseoutRowsModeLiteralPrefix.machine (emit false)
noncomputable def b:=Composition.machine a (mark true)
noncomputable def c:=Composition.machine b (TapeEmbedding.machine 1 RowMaskBody.machine)
noncomputable def d:=Composition.machine c (mark false)
noncomputable def machine:=Composition.machine d (emit false)
def budget (index : Nat):=4*index+33

theorem word (neg bit : Bool) (index : Nat) (out : List Bool) :
    (((((out++CloseoutRowsModeLiteralPrefix.constant neg)++[false])++emitted bit true)++
      RowMaskBody.emitted bit (index+1))++emitted bit false)++[false]=
      out++CloseoutRowsRawPairSeek.word (pair neg bit index):=by
  cases neg <;> cases bit <;>
    simp [pair,CloseoutRowsRawPairSeek.word,CloseoutRowsModeLiteralPrefix.constant,emitted,
      RowMaskBody.emitted,ExtIncidence.stream,ExtIncidence.monomialWord,ExtIncidence.block,
      RowIndexField.word,List.append_assoc]

theorem pair_run (neg bit : Bool) (pre tail out : List Bool) (index count : Nat) :
    Step machine (budget index) (heads pre.length (index+1) count out)
      (data (pre++bit::tail) (index+1) count out neg)
      (heads (pre.length+1) (index+2) (count+bit.toNat) (out++CloseoutRowsRawPairSeek.word (pair neg bit index)))
      (data (pre++bit::tail) (index+2) (count+bit.toNat)
        (out++CloseoutRowsRawPairSeek.word (pair neg bit index)) bit):=by
  let o1:=out++CloseoutRowsModeLiteralPrefix.constant neg
  let o2:=o1++[false]
  let o3:=o2++emitted bit true
  let o4:=o3++RowMaskBody.emitted bit (index+1)
  let o5:=o4++emitted bit false
  have p:=CloseoutRowsModeLiteralPrefix.prefix_run neg (pre++bit::tail) out pre.length (index+1) count
  have q:=emit_run false neg (pre++bit::tail) o1 pre.length (index+1) count
  have r:=mark_run true bit neg (pre++bit::tail) o2 pre.length (index+1) count (Streaming.read_append pre tail bit)
  obtain ⟨receipt,hr,rh,rt,_⟩:=RowMaskBody.body_run pre tail bit (index+1) count o3
  have s:=(Step.of_run hr rh rt).embed (fun _ : Fin 1=>0) (fun _=>[bit])
  have t:=mark_run false (readTapeBit (pre++bit::tail) (pre.length+1)) bit
    (pre++bit::tail) o4 (pre.length+1) (index+2) (count+bit.toNat) rfl
  have u:=emit_run false bit (pre++bit::tail) o5 (pre.length+1) (index+2) (count+bit.toNat)
  have raw:=((((p.seq q).seq r).seq s).seq t).seq u
  have time:((((2+1+1)+1+1)+1+(4*(index+1)+18))+1+1)+1+1=budget index:=by unfold budget;omega
  rw [time] at raw
  simpa only [machine,d,c,b,a,o1,o2,o3,o4,o5,word,Nat.add_assoc] using raw

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralPair
