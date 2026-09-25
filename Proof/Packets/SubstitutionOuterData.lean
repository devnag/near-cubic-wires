import Proof.Packets.SubstitutionScan
import Proof.Packets.VectorAccumulatorRight
import Proof.Packets.VectorOperandCopies

/-! Shared physical arena for exact monomial substitution. Tapes39/40 hold the
outer sum; tapes41/42 retain the physically generated constant-one packet. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
abbrev Packet := List (List Bool)
def one (C : Nat) : Packet := [List.replicate C false]
def H (position indexHead : Nat) : Fin 43→Nat :=
  Fin.addCases (m:=34) (n:=9) ReusableArithmetic.heads
    (![0,indexHead,0,position,1,0,0,0,0])
def extras (C R index : Nat) (atoms source : List Bool) (stored : Packet) (i : Fin 9) : List Bool :=
  if i=5 then ZeroPadding.pad R stored.flatten else
  if i=6 then ZeroPadding.pad R (CompareMachine.word stored.length) else
    (![atoms,ZeroPadding.pad R (CompareMachine.word index),List.replicate R false,source,
      CompareMachine.word C,[],[],ZeroPadding.pad R (one C).flatten,
      ZeroPadding.pad R (CompareMachine.word (one C).length)] : Fin 9→List Bool) i

def A (C R index : Nat) (left right : Packet) (atoms source : List Bool) (stored : Packet) : Fin 43→List Bool :=
  Fin.addCases (m:=34) (n:=9) (ReusableArithmetic.state C R left right)
    (extras C R index atoms source stored)

theorem A_core (C R index : Nat) (left right : Packet) (atoms source : List Bool) (stored : Packet) (i : Fin 34) :
    A C R index left right atoms source stored (i.castAdd 9)=ReusableArithmetic.state C R left right i :=
  Fin.addCases_left _
theorem A_extra (C R index : Nat) (left right : Packet) (atoms source : List Bool) (stored : Packet) (i : Fin 9) :
    A C R index left right atoms source stored (i.natAdd 34)=extras C R index atoms source stored i :=
  Fin.addCases_right _

theorem H_core (position cp : Nat) (i : Fin 34) : H position cp (i.castAdd 9)=ReusableArithmetic.heads i :=
  Fin.addCases_left _
theorem H_extra (position cp : Nat) (i : Fin 9) :
    H position cp (i.natAdd 34)=(![0,cp,0,position,1,0,0,0,0] : Fin 9→Nat) i :=
  Fin.addCases_right _

def accumulatorPorts : Fin 36→Fin 43 := Fin.addCases (m:=34) (n:=2) (fun i=>i.castAdd 9) ![39,40]
def constantPorts : Fin 36→Fin 43 := Fin.addCases (m:=34) (n:=2) (fun i=>i.castAdd 9) ![41,42]

theorem accumulator_core (i : Fin 34) : accumulatorPorts (i.castAdd 2)=i.castAdd 9 := Fin.addCases_left _
theorem accumulator_extra (i : Fin 2) : accumulatorPorts (i.natAdd 34)=(![39,40] : Fin 2→Fin 43) i :=
  Fin.addCases_right _
theorem constant_core (i : Fin 34) : constantPorts (i.castAdd 2)=i.castAdd 9 := Fin.addCases_left _
theorem constant_extra (i : Fin 2) : constantPorts (i.natAdd 34)=(![41,42] : Fin 2→Fin 43) i :=
  Fin.addCases_right _


theorem accumulator_val (i : Fin 36) :
    (accumulatorPorts i).val=if i.val<34 then i.val else i.val+5 := by
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [accumulator_core]
    simp only [Fin.val_castAdd,if_pos j.isLt]
  · rw [accumulator_extra]
    fin_cases j <;>rfl

theorem constant_val (i : Fin 36) :
    (constantPorts i).val=if i.val<34 then i.val else i.val+7 := by
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [constant_core]
    simp only [Fin.val_castAdd,if_pos j.isLt]
  · rw [constant_extra]
    fin_cases j <;>rfl

theorem accumulator_injective : Function.Injective accumulatorPorts := by
  intro i j he
  have hv:=congrArg Fin.val he
  rw [accumulator_val,accumulator_val] at hv
  apply Fin.ext
  split_ifs at hv <;>omega

theorem constant_injective : Function.Injective constantPorts := by
  intro i j he
  have hv:=congrArg Fin.val he
  rw [constant_val,constant_val] at hv
  apply Fin.ext
  split_ifs at hv <;>omega


theorem accumulator_heads (position cp : Nat) :
    (fun i=>H position cp (accumulatorPorts i))=VectorAccumulator.heads := by
  funext i
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [accumulator_core,H_core]
    unfold VectorAccumulator.heads
    rw [Fin.addCases_left]
  · rw [accumulator_extra]
    fin_cases j <;>rfl


theorem accumulator_tapes (C R index : Nat) (left right : Packet) (atoms source : List Bool) (stored : Packet) :
    (fun i=>A C R index left right atoms source stored (accumulatorPorts i))=
      VectorAccumulator.tapes C R left right stored := by
  funext i
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [accumulator_core,A_core]
    unfold VectorAccumulator.tapes
    rw [Fin.addCases_left]
  · rw [accumulator_extra]
    fin_cases j <;>rfl


set_option maxHeartbeats 120000 in
theorem dock_accumulator {s fuel : Nat} {p : Machine 36 s}
    (C R index position cp : Nat) (left right stored left' right' stored' : Packet) (atoms source : List Bool)
    (h : Step p fuel VectorAccumulator.heads (VectorAccumulator.tapes C R left right stored)
      VectorAccumulator.heads (VectorAccumulator.tapes C R left' right' stored')) :
    Step (RecoveryFocus.machine accumulatorPorts p) fuel (H position cp)
      (A C R index left right atoms source stored) (H position cp)
      (A C R index left' right' atoms source stored') := by
  apply PhysicalFocusBoundary.focus h accumulatorPorts accumulator_injective (H position cp) (H position cp) _ _
  · intro i;exact (congrFun (accumulator_heads position cp) i).symm
  · intro i;exact (congrFun (accumulator_tapes C R index left right atoms source stored) i).symm
  · intro i;exact (congrFun (accumulator_heads position cp) i).symm
  · intro i;exact (congrFun (accumulator_tapes C R index left' right' atoms source stored') i).symm
  · intro i away
    refine ⟨rfl,?_⟩
    revert away
    refine Fin.addCases (m:=34) (n:=9) (fun j=>?_) (fun j=>?_) i
    · intro away
      exact False.elim (away (j.castAdd 2) (accumulator_core j))
    · intro away
      rw [A_extra,A_extra]
      have h5 : j≠5 := by intro hj;subst j;exact away 34 (accumulator_extra 0)
      have h6 : j≠6 := by intro hj;subst j;exact away 35 (accumulator_extra 1)
      simp only [extras,if_neg h5,if_neg h6]


theorem constant_heads (position cp : Nat) :
    (fun i=>H position cp (constantPorts i))=VectorAccumulator.heads := by
  funext i
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [constant_core,H_core]
    unfold VectorAccumulator.heads
    rw [Fin.addCases_left]
  · rw [constant_extra]
    fin_cases j <;>rfl


theorem constant_tapes (C R index : Nat) (left right : Packet) (atoms source : List Bool) (stored : Packet) :
    (fun i=>A C R index left right atoms source stored (constantPorts i))=
      VectorAccumulator.tapes C R left right (one C) := by
  funext i
  refine Fin.addCases (m:=34) (n:=2) (fun j=>?_) (fun j=>?_) i
  · rw [constant_core,A_core]
    unfold VectorAccumulator.tapes
    rw [Fin.addCases_left]
  · rw [constant_extra]
    fin_cases j <;>rfl


set_option maxHeartbeats 120000 in
theorem dock_constant {s fuel : Nat} {p : Machine 36 s}
    (C R index position cp : Nat) (left right left' right' stored : Packet) (atoms source : List Bool)
    (h : Step p fuel VectorAccumulator.heads (VectorAccumulator.tapes C R left right (one C))
      VectorAccumulator.heads (VectorAccumulator.tapes C R left' right' (one C))) :
    Step (RecoveryFocus.machine constantPorts p) fuel (H position cp)
      (A C R index left right atoms source stored) (H position cp)
      (A C R index left' right' atoms source stored) := by
  apply PhysicalFocusBoundary.focus h constantPorts constant_injective (H position cp) (H position cp) _ _
  · intro i;exact (congrFun (constant_heads position cp) i).symm
  · intro i;exact (congrFun (constant_tapes C R index left right atoms source stored) i).symm
  · intro i;exact (congrFun (constant_heads position cp) i).symm
  · intro i;exact (congrFun (constant_tapes C R index left' right' atoms source stored) i).symm
  · intro i away
    refine ⟨rfl,?_⟩
    revert away
    refine Fin.addCases (m:=34) (n:=9) (fun j=>?_) (fun j=>?_) i
    · intro away
      exact False.elim (away (j.castAdd 2) (constant_core j))
    · intro _
      rw [A_extra,A_extra]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
