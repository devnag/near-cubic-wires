import Proof.Packets.CycleArithmeticAllocate
import Proof.Packets.CycleMaskWidth
import Proof.Packets.WindowSeedPrimitives
import Proof.Packets.PhysicalOneOutput
import Proof.Packets.PhysicalIndexReload
import Proof.Packets.ReusableNormalizedArithmetic

/-! Actual cold arithmetic bank: allocate all backing from the resident raw
reserve, compute both width templates from the resident C template, and copy
them into the reusable engine. Every other entry tape is empty. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open Theorem25Completion
noncomputable section

attribute [local irreducible] CycleArithmeticAllocate.machine CycleMaskWidth.machine WindowSeed.copy

def input (C R : Nat) : Fin 46 → List Bool :=
  Fin.addCases (m:=35) (n:=11) (motive:=fun _=>List Bool) (CycleArithmeticAllocate.input R) (CycleMaskWidth.input C)
def allocated (C R : Nat) : Fin 46 → List Bool :=
  Fin.addCases (m:=35) (n:=11) (motive:=fun _=>List Bool) (CycleArithmeticAllocate.output R) (CycleMaskWidth.input C)
def widthed (C R : Nat) : Fin 46 → List Bool :=
  Fin.addCases (m:=35) (n:=11) (motive:=fun _=>List Bool) (CycleArithmeticAllocate.output R) (CycleMaskWidth.output C)
def heads (i : Fin 46) : Nat := if i=31 then 1 else 0
def widthHeads : Fin 46 → Nat := Fin.addCases (m:=35) (n:=11) (motive:=fun _=>Nat) CycleArithmeticAllocate.heads CycleMaskWidth.heads

def allocate := TapeEmbedding.machine 11 CycleArithmeticAllocate.machine
def widths := RecoveryFocus.machine (Fin.natAdd 35) CycleMaskWidth.machine
def lower := PhysicalIndexReload.move (44 : Fin 46) .left
def copySlots (s d : Fin 46) : Fin 4 → Fin 46 := ![s,d,32,33]
def copyAt (s d : Fin 46) := RecoveryFocus.machine (copySlots s d) WindowSeed.copy

def output (C R : Nat) := Function.update
  (Function.update (widthed C R) 24 (ZeroPadding.pad R (UnaryTemplate.tape C)))
  13 (ZeroPadding.pad R (UnaryTemplate.tape (2*C+3)))
def machine := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine allocate widths) lower) (copyAt 35 24)) (copyAt 44 13)
def budget (C R : Nat) := 10*R+16*C+101

theorem allocate_run (C R : Nat) : Step allocate (6*R+24) (fun _=>0) (input C R)
    heads (allocated C R) := by
  have h:=(CycleArithmeticAllocate.run R).embed (fun _ : Fin 11=>0) (CycleMaskWidth.input C)
  have he : Fin.addCases (m:=35) (n:=11) (motive:=fun _=>Nat) CycleArithmeticAllocate.heads (fun _ : Fin 11=>0)=heads := by
    funext i;fin_cases i <;>rfl
  have hi : (Fin.addCases (m:=35) (n:=11) (motive:=fun _=>Nat) (fun _ : Fin 35=>0) (fun _ : Fin 11=>0) : Fin 46→Nat)=(fun _=>0) := by
    funext i;fin_cases i <;>rfl
  exact h.congr_in hi rfl |>.congr he rfl

theorem widths_run (C R : Nat) : Step widths (16*C+64) heads (allocated C R)
    widthHeads (widthed C R) := by
  apply PhysicalFocusBoundary.focus (CycleMaskWidth.run C) (Fin.natAdd 35)
    (by intro i j h;exact Fin.ext (by have e:=congrArg (fun z : Fin 46=>z.val) h;simp only [Fin.val_natAdd] at e;omega))
    heads widthHeads (allocated C R) (widthed C R)
  · intro j;fin_cases j <;>rfl
  · intro j;simp only [allocated,Fin.addCases_right]
  · intro j;simp only [widthHeads,Fin.addCases_right]
  · intro j;simp only [widthed,Fin.addCases_right]
  · intro i away
    revert away
    refine Fin.addCases (m:=35) (n:=11) (fun j=>?_) (fun j=>?_) i
    · intro _;constructor
      · fin_cases j <;>rfl
      · simp only [allocated,widthed,Fin.addCases_left]
    · intro h;exact False.elim (h j rfl)

theorem lower_run (C R : Nat) : Step lower 1 widthHeads (widthed C R) heads (widthed C R) := by
  have h:=PhysicalIndexReload.move_run (44 : Fin 46) .left widthHeads (widthed C R)
  have e : Function.update widthHeads 44 (HeadMove.left.apply (widthHeads 44))=heads := by
    funext i;fin_cases i <;>simp [widthHeads,heads,CycleArithmeticAllocate.heads,CycleMaskWidth.heads,Fin.addCases,HeadMove.apply]
  exact h.congr e rfl

theorem copy_run (R : Nat) (s d : Fin 46) (A : Fin 46→List Bool)
    (hinj : Function.Injective (copySlots s d))
    (hs : heads s=0) (hd : heads d=0) (hsize : (A s).length ≤ R)
    (az : A d=List.replicate R false) (ar : A 32=List.replicate R true)
    (al : A 33=List.replicate (R+3) false) :
    Step (copyAt s d) (2*R+4) heads A heads (Function.update A d (ZeroPadding.pad R (A s))) := by
  have small:=WindowSeed.copy_run R (A s) hsize
  have small' : Step WindowSeed.copy (2*R+4) (fun _=>0)
      (WindowSeed.copyData R (A s) (List.replicate R false)) (fun _=>0)
      (Function.update (WindowSeed.copyData R (A s) (List.replicate R false)) 1 (ZeroPadding.pad R (A s))) := by
    convert small using 1 <;>first | rfl | (funext i;fin_cases i <;>rfl)
  apply PhysicalOneOutput.focus WindowSeed.copy _ _ 1 _ small' (copySlots s d) hinj heads A
  · intro i;fin_cases i <;>first | exact hs | exact hd | rfl
  · intro i;fin_cases i <;>first | exact az | exact ar | exact al | rfl

theorem run (C R : Nat) (hfit : 2*C+5 ≤ R) :
    Step machine (budget C R) (fun _=>0) (input C R) heads (output C R) := by
  have ac : widthed C R 35=UnaryTemplate.tape C:=CycleMaskWidth.source_template C
  have aw : widthed C R 44=UnaryTemplate.tape (2*C+3):=CycleMaskWidth.width_template C
  have lenC : (widthed C R 35).length ≤ R := by rw [ac];simp [UnaryTemplate.tape];omega
  have first:=copy_run R 35 24 (widthed C R) (by decide) rfl rfl lenC rfl rfl rfl
  rw [ac] at first
  let A:=Function.update (widthed C R) 24 (ZeroPadding.pad R (UnaryTemplate.tape C))
  have aw' : A 44=UnaryTemplate.tape (2*C+3):=by simpa only [A,Function.update_of_ne (by decide : (44 : Fin 46)≠24)] using aw
  have lenW : (A 44).length ≤ R := by rw [aw'];simp [UnaryTemplate.tape];omega
  have last:=copy_run R 44 13 A (by decide) rfl rfl lenW (by simp [A,widthed,Fin.addCases,CycleArithmeticAllocate.output,CycleArithmeticAllocate.bank2])
    (by simp [A,widthed,Fin.addCases,CycleArithmeticAllocate.output,CycleArithmeticAllocate.bank2])
    (by simp [A,widthed,Fin.addCases,CycleArithmeticAllocate.output,CycleArithmeticAllocate.bank2])
  rw [aw'] at last
  have all:=((((allocate_run C R).seq (widths_run C R)).seq (lower_run C R)).seq first).seq last
  have fuel : (((6*R+24)+1+(16*C+64))+1+1)+1+(2*R+4)+1+(2*R+4)=budget C R := by unfold budget;omega
  simpa only [machine,output,A,fuel] using all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticCold
