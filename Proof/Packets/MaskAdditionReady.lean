import Proof.Packets.MaskFrameReverse
import Proof.Packets.MaskProductReady

/-! Actual raw addition input: the left bank in reverse record order, then
right bank, with a physically produced total count and all cursors ready. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskAddition
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
abbrev H := MaskProduct.readyH
abbrev A := MaskProduct.readyA
abbrev seekSlots := MaskProduct.leftBackSlots
def reverseSlots : Fin 6→Fin 9 := ![0,8,1,3,4,6]
def frameSlots : Fin 6→Fin 9 := ![0,8,2,3,4,5]
def rightBackSlots : Fin 4→Fin 9 := ![0,2,8,5]
abbrev machine := Composition.machine (RecoveryFocus.machine seekSlots MaskSeek.machine)
  (Composition.machine (RecoveryFocus.machine reverseSlots MaskFrame.reverseLoop)
    (Composition.machine (RecoveryFocus.machine frameSlots MaskFrame.loop)
      (Composition.machine (RecoveryFocus.machine rightBackSlots MaskBack.machine)
        (Composition.machine (RecoveryFocus.machine MaskProduct.countSlots PairCountReady.machine)
          (RecoveryFocus.machine MaskProduct.outputBackSlots MaskBack.machine)))))
def budget (B M N : Nat) :=
  (M*(2*B+5)+3)+1+((M*(7*B+15)+3)+1+((N*(3*B+9)+3)+1+
    ((N*(2*B+5)+3)+1+((M+N+2)+1+((M+N)*(2*(2*B+3)+5)+3)))))
def records (left right : List (List Bool)) := MaskFrame.records left.reverse++MaskFrame.records right

theorem frame_length (B : Nat) (rows : List (List Bool)) (hw : ∀r∈rows,r.length=B) :
    (MaskFrame.records rows).length=rows.length*(2*B+3) := by
  induction rows with
  | nil => simp [MaskFrame.records]
  | cons row rows ih =>
    have hr:=hw row (by simp)
    have ht:=ih (fun r h=>hw r (by simp [h]))
    change (MaskFrame.record row++MaskFrame.records rows).length=_
    simp only [List.length_append,MaskFrame.record,List.length_append,RepairOrdinary.frame_length,
      List.length_cons,List.length_nil,hr,ht]
    ring

theorem ready_run (B : Nat) (left right : List (List Bool))
    (mpre mtail pre tail out : List Bool)
    (hl : ∀ row∈left,row.length=B) (hr : ∀ row∈right,row.length=B) :
    Step machine (budget B left.length right.length)
      (H mpre.length pre.length out.length 1)
      (A B left.length right.length (mpre++left.flatten++mtail)
        (pre++right.flatten++tail) out (CompareMachine.word 0))
      (H mpre.length pre.length out.length 1)
      (A B left.length right.length (mpre++left.flatten++mtail)
        (pre++right.flatten++tail) (out++records left right)
        (CompareMachine.word (left.length+right.length))) := by
  have llen:=MaskProduct.flatten_length B left hl
  have rlen:=MaskProduct.flatten_length B right hr
  have flen:=frame_length B left.reverse (fun r h=>hl r (by simpa using h))
  have glen:=frame_length B right hr
  simp only [List.length_reverse] at flen
  let mid:=out++MaskFrame.records left.reverse
  let final:=mid++MaskFrame.records right
  obtain ⟨r,rr,rf,_⟩:=MaskSeek.seek_run B left.length mpre.length (mpre++left.flatten++mtail) []
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have first:=PhysicalFocusBoundary.focus rs seekSlots (by decide)
    (H mpre.length pre.length out.length 1)
    (H (mpre.length+left.length*B) pre.length out.length 1)
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      out (CompareMachine.word 0))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      out (CompareMachine.word 0))
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))
  obtain ⟨r,rr,rf,_⟩:=MaskFrame.reverse_run B left mpre mtail out (CompareMachine.word 0) hl
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have second:=PhysicalFocusBoundary.focus rs reverseSlots (by decide)
    (H (mpre.length+left.length*B) pre.length out.length 1)
    (H mpre.length pre.length mid.length (left.length+1))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      out (CompareMachine.word 0))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      mid (CompareMachine.word left.length))
    (by intro i;fin_cases i <;> first | rfl |
      (change mpre.length+left.flatten.length=mpre.length+left.length*B;rw [llen]))
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> first | rfl |
      (change (CompareMachine.word 0++List.replicate left.length true).length=left.length+1
       simp [CompareMachine.word]))
    (by intro i;fin_cases i <;> rfl)
    (by
      intro i away;fin_cases i
      all_goals first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl) |
        exact False.elim (away 3 rfl) | exact False.elim (away 4 rfl))
  obtain ⟨r,rr,rf,_⟩:=MaskFrame.loop_run B right [] pre tail mid (CompareMachine.word left.length) hr
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have ceq : CompareMachine.word left.length++List.replicate right.length true=
      CompareMachine.word (left.length+right.length) := by
    simp only [CompareMachine.word,List.cons_append,List.replicate_add]
  have third:=PhysicalFocusBoundary.focus rs frameSlots (by decide)
    (H mpre.length pre.length mid.length (left.length+1))
    (H mpre.length (pre.length+right.length*B) final.length (left.length+right.length+1))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      mid (CompareMachine.word left.length))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      final (CompareMachine.word (left.length+right.length)))
    (by intro i;fin_cases i <;> first | rfl |
      (change (CompareMachine.word left.length).length=left.length+1;simp [CompareMachine.word]))
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> first | rfl |
      (change pre.length+right.flatten.length=pre.length+right.length*B;rw [rlen]) |
      (change (CompareMachine.word left.length++List.replicate right.length true).length=
        left.length+right.length+1;rw [ceq];simp [CompareMachine.word]))
    (by intro i;fin_cases i <;> first | rfl | exact ceq)
    (by
      intro i away;fin_cases i
      all_goals first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl) |
        exact False.elim (away 3 rfl) | exact False.elim (away 4 rfl))
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run B right.length pre.length (pre++right.flatten++tail) []
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have fourth:=PhysicalFocusBoundary.focus rs rightBackSlots (by decide)
    (H mpre.length (pre.length+right.length*B) final.length (left.length+right.length+1))
    (H mpre.length pre.length final.length (left.length+right.length+1))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      final (CompareMachine.word (left.length+right.length)))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      final (CompareMachine.word (left.length+right.length)))
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))
  obtain ⟨r,rr,rf,_⟩:=PairCountReady.run (left.length+right.length)
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have fifth:=PhysicalFocusBoundary.focus rs MaskProduct.countSlots (by decide)
    (H mpre.length pre.length final.length (left.length+right.length+1))
    (H mpre.length pre.length final.length 1)
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      final (CompareMachine.word (left.length+right.length)))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      final (CompareMachine.word (left.length+right.length)))
    (by intro i;fin_cases i; rfl) (by intro i;fin_cases i; rfl)
    (by intro i;fin_cases i; rfl) (by intro i;fin_cases i; rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl))
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run (2*B+3) (left.length+right.length) out.length final []
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have sixth:=PhysicalFocusBoundary.focus rs MaskProduct.outputBackSlots (by decide)
    (H mpre.length pre.length final.length 1)
    (H mpre.length pre.length out.length 1)
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      final (CompareMachine.word (left.length+right.length)))
    (A B left.length right.length (mpre++left.flatten++mtail) (pre++right.flatten++tail)
      final (CompareMachine.word (left.length+right.length)))
    (by intro i;fin_cases i <;> first | rfl |
      (change out.length+(left.length+right.length)*(2*B+3)=final.length
       simp only [final,mid,List.length_append,flen,glen]
       ring))
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))
  have h:=first.seq (second.seq (third.seq (fourth.seq (fifth.seq sixth))))
  simpa only [machine,budget,final,mid,records,List.append_assoc] using h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MaskAddition
