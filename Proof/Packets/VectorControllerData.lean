import Proof.Packets.VectorControllerLayout

/-! Exact tape boundaries for the provider/vector controller. Provider-only
fields are retained literally while the child transaction changes arithmetic
operands and saved parent accumulator. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorController
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def extraHeads : Fin 8→Nat := ![0,0,1,1,1,0,0,0]
def extraTapes (R ci pi li : Nat) (acc : List (List Bool)) (previous next : List Bool) (i : Fin 8) : List Bool :=
  if i=0 then previous else if i=1 then next else if i=5 then ZeroPadding.pad R acc.flatten
  else if i=6 then ZeroPadding.pad R (CompareMachine.word acc.length)
  else (![[],[],ZeroPadding.pad R (CompareMachine.word ci),ZeroPadding.pad R (CompareMachine.word pi),
    ZeroPadding.pad R (CompareMachine.word li),[],[],List.replicate R false] : Fin 8→List Bool) i

def H (mh : Fin 222→Nat) : Fin 264→Nat := Fin.addCases (m:=256) (n:=8) (motive:=fun _=>Nat)
  (Fin.addCases (m:=34) (n:=222) (motive:=fun _=>Nat) ReusableArithmetic.heads mh) extraHeads
def A (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) : Fin 264→List Bool :=
  Fin.addCases (m:=256) (n:=8) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=34) (n:=222) (motive:=fun _=>List Bool) (ReusableArithmetic.state B R left right) fields)
    (extraTapes R ci pi li acc previous next)

theorem H_core (mh : Fin 222→Nat) (i : Fin 34) : H mh (i.castAdd 230)=ReusableArithmetic.heads i := by
  calc
    _=(Fin.addCases (m:=34) (n:=222) (motive:=fun _=>Nat) ReusableArithmetic.heads mh) (i.castAdd 222) :=
      Fin.addCases_left (i.castAdd 222)
    _=_ := Fin.addCases_left i

theorem A_core (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (i : Fin 34) :
    A B R ci pi li left right acc previous next fields (i.castAdd 230)=ReusableArithmetic.state B R left right i := by
  calc
    _=(Fin.addCases (m:=34) (n:=222) (motive:=fun _=>List Bool) (ReusableArithmetic.state B R left right) fields) (i.castAdd 222) :=
      Fin.addCases_left (i.castAdd 222)
    _=_ := Fin.addCases_left i
theorem A_meta (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (i : Fin 222) :
    A B R ci pi li left right acc previous next fields ((i.natAdd 34).castAdd 8)=fields i := by
  unfold A
  simp only [Fin.addCases_left,Fin.addCases_right]
theorem A_extra (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (i : Fin 8) :
    A B R ci pi li left right acc previous next fields (i.natAdd 256)=extraTapes R ci pi li acc previous next i :=
  Fin.addCases_right i

theorem child_heads (mh : Fin 222→Nat) (i : Fin 39) :
    VectorChildTransaction.heads i=H mh (childSlots i) := by
  refine Fin.addCases (m:=34) (n:=5) (fun j=>?_) (fun j=>?_) i
  · rw [childSlots_core,H_core,VectorChildTransaction.heads_core]
  · rw [childSlots_extra];fin_cases j <;>rfl

theorem child_tapes (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (i : Fin 39) :
    VectorChildTransaction.tapes B R ci left right acc previous i=
      A B R ci pi li left right acc previous next fields (childSlots i) := by
  refine Fin.addCases (m:=34) (n:=5) (fun j=>?_) (fun j=>?_) i
  · rw [childSlots_core,A_core,VectorChildTransaction.tapes_core]
  · rw [childSlots_extra];fin_cases j <;>rfl

theorem A_child_outside (B R ci pi li : Nat) (left right acc left' right' acc' : List (List Bool))
    (previous next : List Bool) (fields : Fin 222→List Bool) (i : Fin 264) (away : ∀ j,childSlots j≠i) :
    A B R ci pi li left right acc previous next fields i=A B R ci pi li left' right' acc' previous next fields i := by
  revert away
  refine Fin.addCases (m:=256) (n:=8) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=34) (n:=222) (fun k=>?_) (fun k=>?_) j
    · intro away;exact False.elim (away (k.castAdd 5) (childSlots_core k))
    · intro _;rw [A_meta,A_meta]
  · intro away
    have h5 : j≠5 := by intro he;subst j;exact away 37 rfl
    have h6 : j≠6 := by intro he;subst j;exact away 38 rfl
    rw [A_extra,A_extra]
    simp only [extraTapes,if_neg h5,if_neg h6]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorController
