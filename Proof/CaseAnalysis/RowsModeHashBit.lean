import Proof.CaseAnalysis.RowsModeWindowBinomial
import Proof.CaseAnalysis.RowsModeWindowCounterLayout

/-! One Toeplitz output bit scans the original lower diagonals backwards
and upper diagonals forwards. No row matrix or reversed seed is supplied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashBit
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 7 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q bits=>
    if q=0 then some ⟨1,fun i=>if i=6 then some (bits 5) else none,fun _=>.stay⟩
    else if q=1 then some ⟨if bits 4 then 1 else 2,
      fun i=>if i=6 then some (xor (bits 6) (bits 1&&bits 2)) else none,
      ![.right,.right,.left,.stay,.left,.stay,.stay]⟩
    else if q=2 then some (if bits 0 then ⟨2,
      fun i=>if i=6 then some (xor (bits 6) (bits 1&&bits 3)) else none,
      ![.right,.right,.stay,.right,.stay,.stay,.stay]⟩
      else ⟨3,fun _=>none,fun _=>.stay⟩)
    else none

def data (rank row : Nat) (label lower upper translation : List Bool) (acc : Bool) : Fin 7→List Bool:=
  ![List.replicate rank true,label,lower,upper,CompareMachine.word row,translation,[acc]]
def heads (row c : Nat) : Fin 7→Nat:=![c,c,row-c,c-(row+1),row-c,row,0]
def cfg (q : Fin 4) (rank row c : Nat) (label lower upper translation : List Bool) (acc : Bool) : Configuration 7 4:=
  ⟨q,heads row c,data rank row label lower upper translation acc⟩
def phase (row c : Nat) : Fin 4:=if c≤row then 1 else 2
def term (row c : Nat) (label lower upper : List Bool):=
  readTapeBit label c && if c≤row then readTapeBit lower (row-c) else readTapeBit upper (c-(row+1))
def fold (row : Nat) (label lower upper : List Bool) (cs : List Nat) (acc : Bool):=
  cs.foldl (fun b c=>xor b (term row c label lower upper)) acc

theorem row_mark (row c : Nat) (hc : c≤row) :
    readTapeBit (CompareMachine.word row) (row-c)=decide (c<row):=by
  by_cases h:c=row
  · subst c;simp
  · obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (show row-c≠0 by omega)
    rw [hk,CompareMachine.read_mark]
    simp only [show k<row by omega,show c<row by omega]

theorem lower_step (rank row c : Nat) (label lower upper translation : List Bool) (acc : Bool) (hc : c≤row) :
    step machine (cfg 1 rank row c label lower upper translation acc)=
      some (cfg (phase row (c+1)) rank row (c+1) label lower upper translation (xor acc (term row c label lower upper))):=by
  simp only [step,machine,cfg,Configuration.scanned,data,heads,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,if_true]
  apply congrArg some
  apply configuration_ext
  · change (if readTapeBit (CompareMachine.word row) (row-c) then (1 : Fin 4) else 2)=phase row (c+1)
    rw [row_mark row c hc]
    simp only [phase,decide_eq_true_eq]
    congr 1
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply] <;> omega
  · funext i;fin_cases i <;> simp [applyAction,term,hc,writeTapeBit,readTapeBit,List.getD]

theorem upper_step (rank row c : Nat) (label lower upper translation : List Bool) (acc : Bool)
    (hrow : row<c) (hc : c<rank) :
    step machine (cfg 2 rank row c label lower upper translation acc)=
      some (cfg 2 rank row (c+1) label lower upper translation (xor acc (term row c label lower upper))):=by
  have hdriver:readTapeBit (List.replicate rank true) c=true:=by rw [ClockUnaryProduct.read_unary];simp [hc]
  simp only [step,machine,cfg,Configuration.scanned,data,heads,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,hdriver,if_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply] <;> omega
  · funext i;fin_cases i <;> simp [applyAction,term,show ¬c≤row by omega,writeTapeBit,readTapeBit,List.getD]

theorem stop_step (rank row : Nat) (label lower upper translation : List Bool) (acc : Bool) :
    step machine (cfg 2 rank row rank label lower upper translation acc)=
      some (cfg 3 rank row rank label lower upper translation acc):=by
  have hdriver:readTapeBit (List.replicate rank true) rank=false:=by rw [ClockUnaryProduct.read_unary];simp
  simp only [step,machine,cfg,Configuration.scanned,data,heads,Matrix.cons_val_zero,hdriver,if_true]
  rfl

theorem loop (rank row c n : Nat) (label lower upper translation : List Bool) (acc : Bool)
    (hrow : row<rank) (hn : c+n=rank) :
    Timed machine (n+1) (cfg (phase row c) rank row c label lower upper translation acc)
      (cfg 3 rank row rank label lower upper translation (fold row label lower upper (List.range' c n) acc)):=by
  induction n generalizing c acc with
  | zero=>
    have e:c=rank:=by omega
    subst c
    simpa [phase,show ¬rank≤row by omega,fold] using Timed.single (by rfl) (stop_step rank row label lower upper translation acc)
  | succ n ih=>
    have next:step machine (cfg (phase row c) rank row c label lower upper translation acc)=
        some (cfg (phase row (c+1)) rank row (c+1) label lower upper translation (xor acc (term row c label lower upper))):=by
      by_cases hc:c≤row
      · simpa only [phase,hc,if_true] using lower_step rank row c label lower upper translation acc hc
      · have hc':¬c+1≤row:=by omega
        simpa only [phase,hc,hc',if_false] using upper_step rank row c label lower upper translation acc (by omega) (by omega)
    have first:=Timed.single (by unfold machine phase;split <;> rfl) next
    have rest:=ih (c+1) (xor acc (term row c label lower upper)) (by omega)
    have whole:=first.trans rest
    simpa only [fold,List.range'_succ,List.foldl_cons,Nat.add_comm 1] using whole

theorem start_step (rank row : Nat) (label lower upper translation : List Bool) (old : Bool) :
    step machine (cfg 0 rank row 0 label lower upper translation old)=
      some (cfg 1 rank row 0 label lower upper translation (readTapeBit translation row)):=by
  simp only [step,machine,cfg,Configuration.scanned,data,heads,Matrix.cons_val_zero,if_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> simp [applyAction,writeTapeBit]

theorem hash_run (rank row : Nat) (label lower upper translation : List Bool) (old : Bool) (hr : row<rank) :
    ∃ r,runFrom machine (rank+2) (cfg 0 rank row 0 label lower upper translation old)=some r ∧
      r.final=cfg 3 rank row rank label lower upper translation
        (fold row label lower upper (List.range rank) (readTapeBit translation row)) ∧r.steps=rank+2:=by
  have first:=Timed.single (by rfl) (start_step rank row label lower upper translation old)
  have rest:=loop rank row 0 rank label lower upper translation (readTapeBit translation row) hr (by omega)
  simp only [phase,Nat.zero_le,if_true,←List.range_eq_range'] at rest
  have whole:=first.trans rest
  have time:1+(rank+1)=rank+2:=by omega
  rw [time] at whole
  exact whole.run (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashBit
