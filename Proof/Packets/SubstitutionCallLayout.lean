import Proof.Packets.SubstitutionPrepareCopies
import Proof.Packets.SubstitutionOuterLoop

/-! Identification of physically prepared tape words with the padded loop ABI. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def loopHeads (position : Nat) : Fin 44→Nat :=
  Fin.addCases (m:=43) (n:=1) (SubstitutionOuter.H position 1) (fun _=>1)
def loopRaw (C R M : Nat) (left stored : Packet) (atoms source : List Bool) : Fin 44→List Bool :=
  Fin.addCases (m:=43) (n:=1) (SubstitutionOuter.A C R C left (SubstitutionOuter.one C) atoms source stored)
    (fun _=>CompareMachine.word M)
def loopPads (R : Nat) (i : Fin 44) := if i=37 ∨ i=38 ∨ i=43 then R else 0
def loopTapes (C R M : Nat) (left stored : Packet) (atoms source : List Bool) (i : Fin 44) :=
  ZeroPadding.pad (loopPads R i) (loopRaw C R M left stored atoms source i)

theorem resident_core (C R : Nat) (left right : Packet) (atoms : List Bool) (i : Fin 34) :
    resident C R left right atoms (i.castAdd 10)=ReusableArithmetic.state C R left right i := Fin.addCases_left _
theorem resident_extra (C R : Nat) (left right : Packet) (atoms : List Bool) (i : Fin 10) :
    resident C R left right atoms (i.natAdd 34)=(if i=0 then atoms else List.replicate R false) := Fin.addCases_right _

theorem pad_false (C R : Nat) (h : C≤R) :
    ZeroPadding.pad R (List.replicate C false)=List.replicate R false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le h]

theorem one_flat (C R : Nat) (h : C≤R) :
    ZeroPadding.pad R (SubstitutionOuter.one C).flatten=List.replicate R false := by
  simpa [SubstitutionOuter.one] using pad_false C R h

theorem loop_core (C R M : Nat) (left stored : Packet) (atoms source : List Bool) (i : Fin 34) :
    loopTapes C R M left stored atoms source (i.castAdd 10)=ReusableArithmetic.state C R left (SubstitutionOuter.one C) i := by
  have e : i.castAdd 10=(i.castAdd 9).castAdd 1 := rfl
  have hn (n : Fin 44) (h : 34≤n.val) : i.castAdd 10≠n := by
    intro he;have hv:=congrArg (fun x : Fin 44=>x.val) he;have hi:=i.isLt
    simp only [Fin.val_castAdd] at hv;omega
  have hp : loopPads R (i.castAdd 10)=0 := by
    simp only [loopPads,hn 37 (by decide),hn 38 (by decide),hn 43 (by decide),or_self,if_false]
  rw [loopTapes,hp,ZeroPadding.pad_zero,e]
  unfold loopRaw
  rw [Fin.addCases_left,SubstitutionOuter.A_core]

theorem loop_extra (C R M : Nat) (left stored : Packet) (atoms source : List Bool) (hC : C≤R) (i : Fin 10) :
    loopTapes C R M left stored atoms source (i.natAdd 34)=
      (![atoms,ZeroPadding.pad R (CompareMachine.word C),List.replicate R false,
        ZeroPadding.pad R source,ZeroPadding.pad R (CompareMachine.word C),
        ZeroPadding.pad R stored.flatten,ZeroPadding.pad R (CompareMachine.word stored.length),
        List.replicate R false,ZeroPadding.pad R (CompareMachine.word 1),
        ZeroPadding.pad R (CompareMachine.word M)] : Fin 10→List Bool) i := by
  refine Fin.addCases (m:=9) (n:=1) (fun j=>?_) (fun j=>?_) i
  · have e : (j.castAdd 1).natAdd 34=(j.natAdd 34).castAdd 1 := rfl
    unfold loopTapes
    rw [e]
    have hr : loopRaw C R M left stored atoms source ((j.natAdd 34).castAdd 1)=
        SubstitutionOuter.extras C R C atoms source stored j := by
      unfold loopRaw
      rw [Fin.addCases_left,SubstitutionOuter.A_extra]
    rw [hr]
    fin_cases j <;> simp [loopPads,SubstitutionOuter.extras,SubstitutionOuter.one,one_flat,pad_false C R hC]
  · fin_cases j
    change ZeroPadding.pad R (CompareMachine.word M)=_
    rfl

theorem prepared_core (C R : Nat) (left right : Packet) (atoms : List Bool) (hC : C≤R) (i : Fin 34) :
    prepared C R left right atoms (i.castAdd 10)=ReusableArithmetic.state C R left (SubstitutionOuter.one C) i := by
  by_cases h26 : i=26
  · subst i
    change List.replicate R false=ZeroPadding.pad R (SubstitutionOuter.one C).flatten
    exact (one_flat C R hC).symm
  by_cases h27 : i=27
  · subst i;rfl
  have hs (n : Fin 44) (hn : 34≤n.val) : i.castAdd 10≠n := by
    intro he;have hv:=congrArg Fin.val he;have hi:=i.isLt;simp only [Fin.val_castAdd] at hv;omega
  have hi26 : i.castAdd 10≠(26 : Fin 44) := by intro he;apply h26;apply Fin.ext;exact congrArg (fun x : Fin 44=>x.val) he
  have hi27 : i.castAdd 10≠(27 : Fin 44) := by intro he;apply h27;apply Fin.ext;exact congrArg (fun x : Fin 44=>x.val) he
  simp only [prepared,productOne,oneCount,widthCopied,inputCopied,
    Function.update_of_ne hi26,Function.update_of_ne hi27,
    Function.update_of_ne (hs 42 (by decide)),Function.update_of_ne (hs 38 (by decide)),
    Function.update_of_ne (hs 35 (by decide)),Function.update_of_ne (hs 43 (by decide)),
    Function.update_of_ne (hs 37 (by decide)),resident_core]
  have h:=VectorAccumulator.tapes_right_outside C R left right (SubstitutionOuter.one C) [] (i.castAdd 2)
    (by intro he;apply h26;apply Fin.ext;exact congrArg (fun x : Fin 36=>x.val) he)
    (by intro he;apply h27;apply Fin.ext;exact congrArg (fun x : Fin 36=>x.val) he)
  simpa only [VectorAccumulator.tapes_engine] using h

theorem prepared_eq (C R : Nat) (left right : Packet) (atoms : List Bool) (hC : C+2≤R) :
    prepared C R left right atoms=loopTapes C R right.length left [] atoms right.flatten := by
  have h24 : ReusableArithmetic.state C R left right 24=ZeroPadding.pad R (UnaryTemplate.tape C) := rfl
  have h26 : ReusableArithmetic.state C R left right 26=ZeroPadding.pad R right.flatten := rfl
  have h27 : ReusableArithmetic.state C R left right 27=ZeroPadding.pad R (CompareMachine.word right.length) := rfl
  have hblank : ZeroPadding.pad R ([] : List Bool)=List.replicate R false := by simp [ZeroPadding.pad]
  have hzero : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
    exact pad_false 1 R (by omega)
  funext i
  refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
  · rw [prepared_core C R left right atoms (by omega),loop_core]
  · rw [loop_extra C R right.length left [] atoms right.flatten (by omega)]
    fin_cases j <;> simp [prepared,productOne,oneCount,widthCopied,inputCopied,resident,Fin.addCases,
      h24,h26,h27,PhysicalIndexReload.padded_unary_index C R hC,hzero,hblank]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
