import Proof.Rows.NativeGateLoop
import Proof.Rows.FinalPrimeCursor

/-! Count true flags in an actual counted prefix. The circuit's appended
true target flag remains outside that prefix. All increments are paid and
rewound on the same framed binary counter. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CountFlags
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution RadixSemantics SignedSortKey
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def inc:=MaskedReset.machine FinalPrimeCursor.incrMachine (fun _=>true)

theorem increment (w k D :Nat) (hk :k+1<2^w) (hD :2*w+1≤D):
 Step inc (4*w+4) (fun _=>0)
  (![frame (binary w k),List.replicate D false] :Fin 2→List Bool)
  (fun _=>0) (![frame (binary w (k+1)),List.replicate D false] :Fin 2→List Bool) :=by
 let ws:=binary w k
 have hw:ws.length=w:=binary_length _ _
 have hsum:Add.sum ws (List.replicate ws.length false) true=binary w (k+1):=by
  have hl:(Add.sum ws (List.replicate ws.length false) true).length=w:=by
   rw [Add.sum_length _ _ _ (by simp),hw]
  have hv:value (Add.sum ws (List.replicate ws.length false) true)=k+1:=by
   rw [FinalPrimeCursor.incr_value,hw,binary_value w k (by omega),Nat.mod_eq_of_lt hk]
  have h:=BoundedCounter.binary_of_value (Add.sum ws (List.replicate ws.length false) true)
  rw [hl,hv] at h
  exact h.symm
 have h:=(FinalPrimeCursor.incr_step ws).mask (cap:=D) (fun _=>true) (by intro i _;rfl) (by rw [hw];exact hD)
 rw [hsum,hw] at h
 have fuel:2*(2*w+1)+2=4*w+4:=by omega
 rw [fuel] at h
 refine (h.congr_in ?_ ?_).congr ?_ ?_
 all_goals funext i;fin_cases i <;>rfl

def heads (j :Nat):Fin 3→Nat:=![0,0,j]
def bank (w k D :Nat) (source :List Bool):Fin 3→List Bool:=
 Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
  (![frame (binary w k),List.replicate D false] :Fin 2→List Bool) (fun _=>source)
def incrementBody:=TapeEmbedding.machine 1 inc
def guard:=CloseoutRowsOriginalSwitch.machine incrementBody (CloseoutRowsOriginalSwitch.stop 3) 2
def advance:=DecompositionCountPosition.move (fun i :Fin 3=>if i=2 then .right else .stay)
def body:=Composition.machine guard advance

theorem advance_run (w k D j :Nat) (source :List Bool):
 Step advance 1 (heads j) (bank w k D source) (heads (j+1)) (bank w k D source) :=by
 obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
  (fun i :Fin 3=>if i=2 then .right else .stay) (heads j) (bank w k D source)
 apply (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
 · funext i;fin_cases i <;>rfl
 · rfl

def seenCount (xs :List Bool) (j :Nat):=(xs.take j).count true

theorem seenCount_le (xs :List Bool) (j :Nat):seenCount xs j≤j :=by
 have h:(xs.take j).count true≤(xs.take j).length:=List.count_le_length
 unfold seenCount
 exact h.trans (by simp only [List.length_take];omega)

theorem count_next (xs :List Bool) (j :Nat) (hj :j<xs.length):
 seenCount xs (j+1)=seenCount xs j+(if xs.getD j false then 1 else 0) :=by
 unfold seenCount
 rw [List.take_succ_eq_append_getElem hj,List.count_append]
 rw [List.getD_eq_getElem xs false hj]
 cases xs[j] <;>simp

theorem body_run (xs tail :List Bool) (w D j :Nat) (hj :j<xs.length)
 (hw :xs.length<2^w) (hD :2*w+1≤D):
 Step body (4*w+8) (heads j) (bank w (seenCount xs j) D (xs++tail))
  (heads (j+1)) (bank w (seenCount xs (j+1)) D (xs++tail)) :=by
 have hread:readTapeBit (xs++tail) j=xs.getD j false:=by simp [readTapeBit,List.getElem?_append_left hj,hj]
 have bound:=seenCount_le xs j
 have hb:seenCount xs j+1<2^w:=by omega
 have step:Step guard (4*w+6) (heads j) (bank w (seenCount xs j) D (xs++tail))
  (heads j) (bank w (seenCount xs (j+1)) D (xs++tail)):=by
  cases hv:xs.getD j false with
  | false=>
    let cfg:Configuration 3 1:=⟨0,heads j,bank w (seenCount xs j) D (xs++tail)⟩
    let receipt:ExecutionReceipt 3 1:=⟨cfg,0,cfg.tapeCells⟩
    have idle:Step (CloseoutRowsOriginalSwitch.stop 3) 0 (heads j) (bank w (seenCount xs j) D (xs++tail))
     (heads j) (bank w (seenCount xs j) D (xs++tail)):=
      Step.of_run (show runFrom (CloseoutRowsOriginalSwitch.stop 3) 0 cfg=some receipt from rfl) rfl rfl
    have h:=CloseoutRowsOriginalSwitch.false_run incrementBody (CloseoutRowsOriginalSwitch.stop 3) 2 idle
     (show readTapeBit (xs++tail) j=false from hread.trans hv)
    rw [count_next xs j hj,hv]
    simpa only [Bool.false_eq_true,if_false,Nat.add_zero,guard] using h.enlarge (show 2≤4*w+6 by omega)
  | true=>
    have step:=(increment w (seenCount xs j) D hb hD).embed (fun _ :Fin 1=>j) (fun _=>xs++tail)
    have h:=CloseoutRowsOriginalSwitch.true_run incrementBody (CloseoutRowsOriginalSwitch.stop 3) 2 step
     (show readTapeBit (xs++tail) j=true from hread.trans hv)
    rw [count_next xs j hj,hv]
    simp only [if_true]
    rw [show (4*w+4)+2=4*w+6 by omega] at h
    refine (h.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i;fin_cases i <;>rfl
 have h:=step.seq (advance_run w (seenCount xs (j+1)) D j (xs++tail))
 simpa only [body,show (4*w+6)+1+1=4*w+8 by omega] using h

def machine:=RepeatMachine.machine body (fun _ _=>true)
def budget (N w :Nat):=N*(4*w+11)+3

theorem run (xs tail :List Bool) (w D :Nat) (hw :xs.length<2^w) (hD :2*w+1≤D):
 Step machine (budget xs.length w)
  (![0,0,0,1] :Fin 4→Nat)
  (![frame (binary w 0),List.replicate D false,xs++tail,CompareMachine.word xs.length] :Fin 4→List Bool)
  (![0,0,xs.length,1] :Fin 4→Nat)
  (![frame (binary w (xs.count true)),List.replicate D false,xs++tail,CompareMachine.word xs.length] :Fin 4→List Bool) :=by
 have h:=CloseoutRowsOriginalClauseLoop.run body xs.length (4*w+8)
  (fun j=>heads j) (fun j=>bank w (seenCount xs j) D (xs++tail))
  (fun j hj=>body_run xs tail w D j hj hw hD)
 simp only [seenCount,List.take_zero,List.count_nil,List.take_length,show 4*w+8+3=4*w+11 by omega] at h
 refine (h.congr_in ?_ ?_).congr ?_ ?_
 all_goals funext i;fin_cases i <;>rfl
end
end PCJ45bee56da9f34d5a_CountFlags
