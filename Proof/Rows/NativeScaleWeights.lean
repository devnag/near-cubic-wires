import Proof.Rows.NativeScaleRun
import Proof.Rows.FinalNativeResidueWeights

/-! The real counted native-field loop consumes the reusable scaled callback.
Every coefficient is read from the native stream and the scaled framed words
are appended in the same order, with no allocation proportional to the prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleWeights
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open SignedSortKey
noncomputable section

def stream (zs : List Int):=zs.flatMap intWord
def words (a p w : Nat) (zs : List Int) (j : Nat):=
  binary w ((a*FinalPrimeReduce.intResidue p (zs.getD j 0))%p)
def cost (F w U : Nat):=4*F+1024*(w+1)^2+10*U+18*w+53
def budget (N F w U : Nat):=N*(cost F w U+3)+3
def machine:=RepeatMachine.machine (PCJ45bee56da9f34d5a_NativeScaleRun.machine false) (fun _ _=>true)
def heads (pre : List Bool) (zs : List Int) (out : List Bool) (w j : Nat):=
  PCJ45bee56da9f34d5a_NativeScaleInput.heads (pre.length+(stream (zs.take j)).length) (out.length+j*(2*w+1)) 0
def tapes (pre tail : List Bool) (zs : List Int) (out : List Bool) (a p w F U j : Nat):=
  PCJ45bee56da9f34d5a_NativeScaleInput.bank a p w F U (pre++stream zs++tail)
    (out++FinalPrimeModular.blocks (words a p w zs) 0 j) (List.replicate U false)

theorem round (pre tail : List Bool) (zs : List Int) (out : List Bool) (a p w F U j : Nat)
    (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w) (hj : j<zs.length)
    (hF : ∀z∈zs,C10NativeResidueCallback.coreBudget false z w+1≤F)
    (hU : 1024*(w+1)^2+2≤U) :
    Step (PCJ45bee56da9f34d5a_NativeScaleRun.machine false) (cost F w U)
      (heads pre zs out w j) (tapes pre tail zs out a p w F U j)
      (heads pre zs out w (j+1)) (tapes pre tail zs out a p w F U (j+1)):=by
  have hz:zs.getD j 0∈zs:=by rw [List.getD_eq_getElem zs 0 hj];exact List.getElem_mem hj
  let before:=pre++stream (zs.take j)
  let after:=stream (zs.drop (j+1))++tail
  let acc:=out++FinalPrimeModular.blocks (words a p w zs) 0 j
  have h:=PCJ45bee56da9f34d5a_NativeScaleRun.run false before after acc (zs.getD j 0) a p w F U hp hpw ha (hF _ hz) hU
  have bound:PCJ45bee56da9f34d5a_NativeScaleRun.budget false (zs.getD j 0) w F U≤cost F w U:=by
    have hh:=hF _ hz;unfold PCJ45bee56da9f34d5a_NativeScaleRun.budget cost;omega
  have source:before++intWord (zs.getD j 0)++after=pre++stream zs++tail:=by
    rw [stream,CloseoutRowsFamilyLoop.split_word zs 0 intWord j hj]
    simp only [before,after,stream,List.append_assoc]
  have pos:=CloseoutRowsFamilyLoop.next_word zs 0 intWord j hj
  have count:=FinalPrimeModular.blocks_length (words a p w zs) w (fun _=>binary_length _ _) 0 j
  have append:=C10NativeResidueAppend.blocks_snoc (words a p w zs) j
  rw [source] at h
  have nextOut:acc++frame (words a p w zs j)=out++FinalPrimeModular.blocks (words a p w zs) 0 (j+1):=by
    dsimp only [acc];rw [List.append_assoc,append]
  have first:=h.enlarge bound
  refine (first.congr_in ?_ rfl).congr ?_ ?_
  · simp only [before,List.length_append,acc,List.length_append,count,heads]
  · simp only [before,List.length_append,acc,List.length_append,count,heads,stream,pos,
      Nat.add_mul,Nat.one_mul,Bool.false_eq_true,if_false,frame_length,binary_length]
    congr 1 <;>omega
  · exact congrArg (fun o=>PCJ45bee56da9f34d5a_NativeScaleInput.bank a p w F U (pre++stream zs++tail) o (List.replicate U false)) nextOut

theorem run (pre tail : List Bool) (zs : List Int) (out : List Bool) (a p w F U : Nat)
    (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w)
    (hF : ∀z∈zs,C10NativeResidueCallback.coreBudget false z w+1≤F)
    (hU : 1024*(w+1)^2+2≤U) :
    Step machine (budget zs.length F w U)
      (Fin.addCases (m:=91) (n:=1) (motive:=fun _=>Nat)
        (PCJ45bee56da9f34d5a_NativeScaleInput.heads pre.length out.length 0) (fun _=>1))
      (Fin.addCases (m:=91) (n:=1) (motive:=fun _=>List Bool)
        (PCJ45bee56da9f34d5a_NativeScaleInput.bank a p w F U (pre++stream zs++tail) out (List.replicate U false))
        (fun _=>CompareMachine.word zs.length))
      (Fin.addCases (m:=91) (n:=1) (motive:=fun _=>Nat)
        (PCJ45bee56da9f34d5a_NativeScaleInput.heads (pre.length+(stream zs).length) (out.length+zs.length*(2*w+1)) 0) (fun _=>1))
      (Fin.addCases (m:=91) (n:=1) (motive:=fun _=>List Bool)
        (PCJ45bee56da9f34d5a_NativeScaleInput.bank a p w F U (pre++stream zs++tail)
          (out++FinalPrimeModular.blocks (words a p w zs) 0 zs.length) (List.replicate U false))
        (fun _=>CompareMachine.word zs.length)):=by
  have loop:=CloseoutRowsOriginalClauseLoop.run (PCJ45bee56da9f34d5a_NativeScaleRun.machine false) zs.length
    (cost F w U) (heads pre zs out w) (tapes pre tail zs out a p w F U)
    (fun j hj=>round pre tail zs out a p w F U j hp hpw ha hj hF hU)
  simpa only [machine,budget,heads,tapes,List.take_zero,List.take_length,stream,List.flatMap_nil,
    List.length_nil,Nat.add_zero,Nat.zero_mul,FinalPrimeModular.blocks,List.append_nil] using loop

theorem concatenated (a p w : Nat) (zs : List Int) :
    FinalPrimeModular.blocks (words a p w zs) 0 zs.length=
      zs.flatMap (fun z=>frame (binary w ((a*FinalPrimeReduce.intResidue p z)%p))):=by
  rw [C10NativeResidueWeights.blocks_range,←List.range_eq_range']
  simpa only [words] using CloseoutRowsFamilyLoop.flatMap_index zs 0
    (fun z=>frame (binary w ((a*FinalPrimeReduce.intResidue p z)%p)))
end
end PCJ45bee56da9f34d5a_NativeScaleWeights
