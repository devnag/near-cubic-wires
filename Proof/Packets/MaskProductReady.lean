import Proof.Packets.MaskProductOuter
import Proof.Packets.MaskProductCountReady

/-! A fixed nine-tape Cartesian mask producer. The resident raw mask banks,
B and record-width templates, and original row-count drivers are retained.
It returns the emitted support-record bank and its actual unary count with
both consumer cursors at their entry positions. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def outerSlots (i : Fin 7) : Fin 9 := i.castAdd 2
def leftBackSlots : Fin 4→Fin 9 := ![0,1,8,6]
def countSlots : Fin 1→Fin 9 := ![4]
def outputBackSlots : Fin 4→Fin 9 := ![7,3,8,4]
abbrev readyMachine := Composition.machine (RecoveryFocus.machine outerSlots outer)
  (Composition.machine (RecoveryFocus.machine leftBackSlots MaskBack.machine)
    (Composition.machine (RecoveryFocus.machine countSlots PairCountReady.machine)
      (RecoveryFocus.machine outputBackSlots MaskBack.machine)))

def readyH (leftPos rightPos outputPos counterPos : Nat) : Fin 9→Nat :=
  ![1,leftPos,rightPos,outputPos,counterPos,1,1,1,0]
def readyA (B M N : Nat) (left right output counter : List Bool) : Fin 9→List Bool :=
  ![UnaryTemplate.tape B,left,right,output,counter,CompareMachine.word N,
    CompareMachine.word M,UnaryTemplate.tape (2*B+3),[]]
def readyBudget (B M N : Nat) :=
  (M*(budget B N+3)+3)+1+((M*(2*B+5)+3)+1+((M*N+2)+1+(M*N*(2*(2*B+3)+5)+3)))

theorem record_length (B : Nat) (mask bits : List Bool) (hm : mask.length=B) (hb : bits.length=B) :
    (record mask bits).length=2*B+3 := by
  simp [record,values,PhysicalSupportUnion.values,frame_length,hm,hb]

theorem records_length (B : Nat) (mask : List Bool) (right : List (List Bool))
    (hm : mask.length=B) (hr : ∀ r∈right,r.length=B) :
    (records mask right).length=right.length*(2*B+3) := by
  induction right with
  | nil => simp [records]
  | cons r rs ih =>
    have head:=record_length B mask r hm (hr r (by simp))
    have tail:=ih (fun r h=>hr r (by simp [h]))
    change (record mask r++records mask rs).length=_
    rw [List.length_append,head,tail,List.length_cons]
    ring

theorem products_length (B : Nat) (left right : List (List Bool))
    (hl : ∀ r∈left,r.length=B) (hr : ∀ r∈right,r.length=B) :
    (products left right).length=(left.length*right.length)*(2*B+3) := by
  induction left with
  | nil => simp [products]
  | cons mask left ih =>
    have head:=records_length B mask right (hl mask (by simp)) hr
    have tail:=ih (fun r h=>hl r (by simp [h]))
    change (records mask right++products left right).length=_
    rw [List.length_append,head,tail,List.length_cons]
    ring

/-- Actual Cartesian producer, with all nine tape contents and all heads
specified on entry and exit. Output prefix `out` is preserved. -/
theorem ready_run (B : Nat) (left right : List (List Bool))
    (mpre mtail pre tail out : List Bool)
    (hl : ∀ row∈left,row.length=B) (hr : ∀ row∈right,row.length=B) :
    Step readyMachine (readyBudget B left.length right.length)
      (readyH mpre.length pre.length out.length 1)
      (readyA B left.length right.length (mpre++left.flatten++mtail)
        (pre++right.flatten++tail) out (CompareMachine.word 0))
      (readyH mpre.length pre.length out.length 1)
      (readyA B left.length right.length (mpre++left.flatten++mtail)
        (pre++right.flatten++tail) (out++products left right)
        (CompareMachine.word (left.length*right.length))) := by
  have plen:=products_length B left right hl hr
  have llen:=flatten_length B left hl
  obtain ⟨r,rr,rf,_⟩:=outer_run B left right mpre mtail pre tail out (CompareMachine.word 0) hl hr
  have r0:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have first:=PhysicalFocusBoundary.focus r0 outerSlots
    (by intro i j h;exact Fin.ext (congrArg (fun k : Fin 9=>k.val) h))
    (readyH mpre.length pre.length out.length 1)
    (readyH (mpre.length+left.length*B) pre.length (out++products left right).length
      (left.length*right.length+1))
    (readyA B left.length right.length (mpre++left.flatten++mtail)
      (pre++right.flatten++tail) out (CompareMachine.word 0))
    (readyA B left.length right.length (mpre++left.flatten++mtail)
      (pre++right.flatten++tail) (out++products left right)
      (CompareMachine.word (left.length*right.length)))
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> first | rfl |
      (change mpre.length+left.flatten.length=mpre.length+left.length*B;rw [llen]) |
      (change (CompareMachine.word 0++List.replicate (left.length*right.length) true).length=
        left.length*right.length+1;simp [CompareMachine.word]))
    (by intro i;fin_cases i <;> rfl)
    (by
      intro i away;fin_cases i
      all_goals first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl) |
        exact False.elim (away 3 rfl) | exact False.elim (away 4 rfl))
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run B left.length mpre.length (mpre++left.flatten++mtail) []
  have rb:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have second:=PhysicalFocusBoundary.focus rb leftBackSlots (by decide)
    (readyH (mpre.length+left.length*B) pre.length (out++products left right).length
      (left.length*right.length+1))
    (readyH mpre.length pre.length (out++products left right).length (left.length*right.length+1))
    (readyA B left.length right.length (mpre++left.flatten++mtail)
      (pre++right.flatten++tail) (out++products left right) (CompareMachine.word (left.length*right.length)))
    (readyA B left.length right.length (mpre++left.flatten++mtail)
      (pre++right.flatten++tail) (out++products left right) (CompareMachine.word (left.length*right.length)))
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))
  obtain ⟨r,rr,rf,_⟩:=PairCountReady.run (left.length*right.length)
  have rc:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have third:=PhysicalFocusBoundary.focus rc countSlots (by decide)
    (readyH mpre.length pre.length (out++products left right).length (left.length*right.length+1))
    (readyH mpre.length pre.length (out++products left right).length 1)
    (readyA B left.length right.length (mpre++left.flatten++mtail)
      (pre++right.flatten++tail) (out++products left right) (CompareMachine.word (left.length*right.length)))
    (readyA B left.length right.length (mpre++left.flatten++mtail)
      (pre++right.flatten++tail) (out++products left right) (CompareMachine.word (left.length*right.length)))
    (by intro i;fin_cases i; rfl) (by intro i;fin_cases i; rfl)
    (by intro i;fin_cases i; rfl) (by intro i;fin_cases i; rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl))
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run (2*B+3) (left.length*right.length) out.length
    (out++products left right) []
  have ro:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have fourth:=PhysicalFocusBoundary.focus ro outputBackSlots (by decide)
    (readyH mpre.length pre.length (out++products left right).length 1)
    (readyH mpre.length pre.length out.length 1)
    (readyA B left.length right.length (mpre++left.flatten++mtail)
      (pre++right.flatten++tail) (out++products left right) (CompareMachine.word (left.length*right.length)))
    (readyA B left.length right.length (mpre++left.flatten++mtail)
      (pre++right.flatten++tail) (out++products left right) (CompareMachine.word (left.length*right.length)))
    (by intro i;fin_cases i <;> first | rfl |
      (change out.length+(left.length*right.length)*(2*B+3)=(out++products left right).length
       simp only [List.length_append,plen]))
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))
  exact first.seq (second.seq (third.seq fourth))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
