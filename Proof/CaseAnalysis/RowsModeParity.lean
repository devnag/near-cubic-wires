import Proof.CaseAnalysis.RowsModeParityMeaning
import Proof.MachineModel.Runs

/-! A physical simultaneous scan of two equal-width binary fields computes
the Lucas guard. No numerical binomial value or Pascal table is allocated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeParity
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then
      some ⟨if bits 0 then 1 else 2,fun _=>none,![.right,.right,.stay]⟩
    else if q=1 then
      some ⟨0,![none,none,some (bits 2&&(!bits 1||bits 0))],![.right,.right,.stay]⟩
    else none
def cfg (q : Fin 3) (left right : List Bool) (lp rp : Nat) (flag : Bool) : Configuration 3 3:=
  ⟨q,![lp,rp,0],![left,right,[flag]]⟩

theorem marker_step (left right : List Bool) (lp rp : Nat) (old active : Bool)
    (hl : readTapeBit left lp=active) :
    step machine (cfg 0 left right lp rp old)=
      some (cfg (if active then 1 else 2) left right (lp+1) (rp+1) old) := by
  simp [step,machine,cfg,Configuration.scanned,hl]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

theorem payload_step (left right : List Bool) (lp rp : Nat) (old a b : Bool)
    (hl : readTapeBit left lp=a) (hr : readTapeBit right rp=b) :
    step machine (cfg 1 left right lp rp old)=
      some (cfg 0 left right (lp+1) (rp+1) (old&&(!b||a))) := by
  simp [step,machine,cfg,Configuration.scanned,hl,hr]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

theorem scan_prefix (left right preLeft preRight tailLeft tailRight : List Bool) (old : Bool)
    (hlen : left.length=right.length) :
    Timed machine (2*left.length+1)
      (cfg 0 (preLeft++frame left++tailLeft) (preRight++frame right++tailRight)
        preLeft.length preRight.length old)
      (cfg 2 (preLeft++frame left++tailLeft) (preRight++frame right++tailRight)
        (preLeft.length+2*left.length+1) (preRight.length+2*right.length+1)
        (old&&guard left right)) := by
  induction left generalizing right preLeft preRight old with
  | nil =>
      have he:right=[]:=List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst right
      have h:=Timed.single (by rfl : machine.halted 0=false)
        (marker_step (preLeft++frame []++tailLeft) (preRight++frame []++tailRight)
          preLeft.length preRight.length old false
          (by simpa [frame,RepairOrdinary.frame,List.append_assoc] using Streaming.read_append preLeft tailLeft false))
      simpa [guard] using h
  | cons a left ih =>
      cases right with
      | nil => simp at hlen
      | cons b right =>
          let ls:=preLeft++frame (a::left)++tailLeft
          let rs:=preRight++frame (b::right)++tailRight
          have hm : readTapeBit ls preLeft.length=true:=by
            simpa [ls,frame,RepairOrdinary.frame,List.append_assoc] using
              Streaming.read_append preLeft (a::frame left++tailLeft) true
          have ha : readTapeBit ls (preLeft.length+1)=a:=by
            simpa [ls,frame,RepairOrdinary.frame,List.append_assoc] using
              Streaming.read_append (preLeft++[true]) (frame left++tailLeft) a
          have hb : readTapeBit rs (preRight.length+1)=b:=by
            simpa [rs,frame,RepairOrdinary.frame,List.append_assoc] using
              Streaming.read_append (preRight++[true]) (frame right++tailRight) b
          have first:=Timed.single (by rfl : machine.halted 0=false)
            (marker_step ls rs preLeft.length preRight.length old true hm)
          have second:=Timed.single (by rfl : machine.halted 1=false)
            (payload_step ls rs _ _ old a b ha hb)
          have rest:=ih right (preLeft++[true,a]) (preRight++[true,b])
            (old&&(!b||a)) (by simpa using hlen)
          have hel : (preLeft++[true,a])++frame left++tailLeft=ls:=by
            simp [ls,frame,RepairOrdinary.frame,List.append_assoc]
          have her : (preRight++[true,b])++frame right++tailRight=rs:=by
            simp [rs,frame,RepairOrdinary.frame,List.append_assoc]
          rw [hel,her] at rest
          have second' : Timed machine 1 (cfg 1 ls rs (preLeft.length+1) (preRight.length+1) old)
              (cfg 0 ls rs (preLeft++[true,a]).length (preRight++[true,b]).length (old&&(!b||a))):=by
            simpa only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero,Nat.add_assoc] using second
          have all:=first.trans (second'.trans rest)
          have time : 1+(1+(2*left.length+1))=2*(a::left).length+1:=by simp;omega
          rw [time] at all
          simpa [ls,rs,guard,List.length_append,Nat.mul_add,Nat.add_assoc,Nat.add_comm,
            Nat.add_left_comm,Bool.and_assoc] using all

end NearCubicWires.RepairOrdinary.CloseoutRowsModeParity
