import Proof.Rows.Constants

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_Constants
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution

def repeatWord (n : Nat) (word : List Bool) := (List.replicate n word).flatten

@[simp] theorem repeatWord_zero (word : List Bool) : repeatWord 0 word=[] := rfl
@[simp] theorem repeatWord_succ (n : Nat) (word : List Bool) :
    repeatWord (n+1) word=word++repeatWord n word := by
  simp only [repeatWord,List.replicate_succ,List.flatten_cons]
@[simp] theorem repeatWord_empty (n : Nat) : repeatWord n []=[] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatWord_succ, List.nil_append]; exact ih

theorem zeros_add (a b : Nat) : zeros (a+b)=zeros a++zeros b := by
  unfold zeros
  rw [List.replicate_add, List.flatten_append]

theorem repeatWord_zeros (a b : Nat) : repeatWord a (zeros b)=zeros (a*b) := by
  induction a with
  | zero => rw [Nat.zero_mul]; rfl
  | succ a ih =>
    rw [repeatWord_succ,ih,←zeros_add,Nat.succ_mul]
    congr 1
    omega

theorem repeatWord_replicate (a b : Nat) (bit : Bool) :
    repeatWord a (List.replicate b bit)=List.replicate (a*b) bit := by
  induction a with
  | zero => rw [Nat.zero_mul]; rfl
  | succ a ih =>
    rw [repeatWord_succ,ih,←List.replicate_add,Nat.succ_mul]
    congr 1
    omega

theorem binary_zero (n : Nat) : SignedSortKey.binary n 0=List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [SignedSortKey.binary,ih,List.replicate_succ]

theorem frame_true (n : Nat) :
    frame (List.replicate n true)=List.replicate (2*n) true++[false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,frame,ih]
    have hn : 2*(n+1)=2*n+2 := by omega
    rw [hn,List.replicate_succ,List.replicate_succ]
    rfl

theorem double_zero (n : Nat) :
    frame (frame (SignedSortKey.binary n 0))=zeros n++[true,false,false] := by
  rw [binary_zero]
  induction n with
  | zero => rfl
  | succ n ih =>
    change true::true::true::false::frame (frame (List.replicate n false))=_
    rw [ih]
    rfl

theorem double_one (n : Nat) :
    frame (frame (SignedSortKey.binary (n+1) 1))=
      oneBlock++zeros n++[true,false,false] := by
  change true::true::true::true::frame (frame (SignedSortKey.binary n 0))=_
  rw [double_zero]
  rfl

def produced (p n Q C : Nat) (i : Fin 11) : List Bool :=
  blocks 0 i++repeatWord p (blocks 2 i)++repeatWord ((n+1)/2) (blocks 4 i)++
    blocks (if n%2=1 then 7 else 6) i++repeatWord Q (blocks 9 i)++
    repeatWord C (blocks 11 i)++blocks 12 i

theorem pair_true (n : Nat) : repeatWord n [true,true]=List.replicate (2*n) true := by
  have h := repeatWord_replicate n 2 true
  rw [Nat.mul_comm] at h
  exact h

theorem frame_false (n : Nat) :
    frame (List.replicate n false)=repeatWord n [true,false]++[false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true::false::frame (List.replicate n false)=_
    rw [ih]
    rfl

theorem zeros_attach (a b : Nat) (tail : List Bool) :
    zeros a++(zeros b++tail)=zeros (a+b)++tail := by
  rw [←List.append_assoc,←zeros_add]

theorem numeric_zero (p d Q : Nat) :
    zeros 14++repeatWord p (zeros 4)++repeatWord d (zeros 4)++
      repeatWord Q (zeros 2)++[true,false,false]=
      frame (frame (SignedSortKey.binary (2*(Q+2*d+2*p+6)+2) 0)) := by
  simp only [repeatWord_zeros,List.append_assoc,zeros_attach]
  rw [double_zero]
  congr 2
  omega

theorem numeric_one_large (p d Q : Nat) :
    (oneBlock++zeros 13)++repeatWord p (zeros 4)++repeatWord d (zeros 4)++
      repeatWord Q (zeros 2)++[true,false,false]=
      frame (frame (SignedSortKey.binary (2*(Q+2*d+2*p+6)+2) 1)) := by
  simp only [repeatWord_zeros,List.append_assoc,zeros_attach]
  rw [show 2*(Q+2*d+2*p+6)+2=(2*(Q+2*d+2*p+6)+1)+1 by omega, double_one]
  simp only [List.append_assoc]
  congr 3
  omega

theorem numeric_one_small (p d Q : Nat) :
    (oneBlock++zeros 5)++repeatWord p (zeros 2)++repeatWord d (zeros 2)++
      repeatWord Q (zeros 1)++[true,false,false]=
      frame (frame (SignedSortKey.binary (Q+2*d+2*p+6) 1)) := by
  simp only [repeatWord_zeros,List.append_assoc,zeros_attach]
  rw [show Q+2*d+2*p+6=(Q+2*d+2*p+5)+1 by omega, double_one]
  simp only [List.append_assoc]
  congr 3
  omega

theorem produced_fields (p n Q C : Nat) : produced p n Q C=fields p n Q C := by
  funext i
  by_cases h : n%2=1 <;> fin_cases i <;>
    simp [produced,fields,blocks,h,pair_true,frame_true,frame_false] <;>
    first
    | rfl
    | (rw [← numeric_zero]; simp only [List.append_assoc])
    | (rw [← numeric_one_large]; simp only [List.append_assoc])
    | (rw [← numeric_one_small]; simp only [List.append_assoc])

/-- The raw control's exact number of steps; the enclosing Rewind doubles
this once, rather than rewinding each growing output separately. -/
def rawBudget (p n Q C : Nat) := 17*p+n+16*((n+1)/2)+9*Q+3*C+66

end PCJ45bee56da9f34d5a_Constants
