import Proof.MachineModel.Runs
import Proof.PCP.ProjectionDimensionTemplate

/-! A fixed finite program computes c*n+d from one raw unary n. Both constants
are printed by finite control, all intermediate words are physically produced,
and every head returns to zero. Pool seed uses (8,12), (1,1), and (2,0). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Completion.UnaryAffine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization

def templateSlots : Fin 3→Fin 11 := ![0,1,2]
def powerSlots : Fin (DimensionPower.tapes 1)→Fin 11 := ![1,3,4,5,6]
def literalSlots : Fin 2→Fin 11 := ![7,8]
def sumSlots : Fin 4→Fin 11 := ![5,7,9,10]
theorem template_inj : Function.Injective templateSlots := by decide
theorem power_inj : Function.Injective powerSlots := by decide
theorem literal_inj : Function.Injective literalSlots := by decide
theorem sum_inj : Function.Injective sumSlots := by decide

def input (n : Nat) : Fin 11→List Bool := fun i=>if i=0 then List.replicate n true else []
noncomputable def templated (n : Nat) := install templateSlots (input n) (DimensionTemplate.output false n)
noncomputable def afterPower (n : Nat) (P : Fin (DimensionPower.tapes 1)→List Bool) :=
  install powerSlots (templated n) P
noncomputable def afterLiteral (n d : Nat) (P : Fin (DimensionPower.tapes 1)→List Bool) :=
  install literalSlots (afterPower n P) ![List.replicate d true,List.replicate d false]
noncomputable def output (n c d : Nat) (P : Fin (DimensionPower.tapes 1)→List Bool) :=
  install sumSlots (afterLiteral n d P)
    ![List.replicate (c*n) true,List.replicate d true,List.replicate (c*n+d) true,
      List.replicate (c*n+d+2) false]

noncomputable def machine (c d : Nat) := Composition.machine
  (Composition.machine
    (Composition.machine (RecoveryFocus.machine templateSlots (DimensionTemplate.machine false))
      (RecoveryFocus.machine powerSlots (DimensionPower.machine 1 c)))
    (RecoveryFocus.machine literalSlots (HierarchyFixedWord.machine (List.replicate d true))))
  (RecoveryFocus.machine sumSlots ClockUnarySum.machine)
def budget (n c d : Nat) := (2*n+8)+1+DimensionPower.cost c n 1+1+(2*d+2)+1+(2*(c*n+d)+6)

theorem run (n c d : Nat) : ∃ out,
    Step (machine c d) (budget n c d) (fun _=>0) (input n) (fun _=>0) out ∧
      out 0=List.replicate n true ∧ out 9=List.replicate (c*n+d) true := by
  have ht:=(DimensionTemplate.ready false n).focus templateSlots template_inj (input n)
    (by intro i;fin_cases i <;>rfl)
  obtain ⟨P,hp,_,hv⟩:=DimensionPower.power_run 1 c n
  have hpower:=hp.focus powerSlots power_inj (templated n) (by
    intro i
    have hi:i.val<5:=i.isLt
    fin_cases i
    · exact install_slot templateSlots template_inj _ _ 1
    all_goals rw [templated,install_other templateSlots _ _ _ (by decide)]
    all_goals rfl)
  obtain ⟨r,hr,htapes,hheads,hsteps⟩:=HierarchyFixedWord.word_ready (List.replicate d true)
  have literal : ClockJoin.ReadyRun (HierarchyFixedWord.machine (List.replicate d true))
      (2*d+2) (fun _=>[]) ![List.replicate d true,List.replicate d false] := by
    refine ⟨r,?_,?_,hheads,?_⟩
    · simpa only [List.length_replicate] using hr
    · simpa only [List.length_replicate] using htapes
    · simpa only [List.length_replicate] using hsteps.le
  have hliteral:=literal.focus literalSlots literal_inj (afterPower n P) (by
    intro i;fin_cases i
    all_goals rw [afterPower,install_other powerSlots _ _ _ (by decide)]
    all_goals rw [templated,install_other templateSlots _ _ _ (by decide)]
    all_goals rfl)
  have hsum:=(ClockUnarySum.sum_ready (c*n) d).focus sumSlots sum_inj (afterLiteral n d P) (by
    intro i;fin_cases i
    · rw [afterLiteral,install_other literalSlots _ _ _ (by decide)]
      change install powerSlots _ P (powerSlots (DimensionPower.valueSlot 1 1 le_rfl))=_
      rw [install_slot powerSlots power_inj]
      simpa using hv
    · exact install_slot literalSlots literal_inj _ _ 0
    all_goals rw [afterLiteral,install_other literalSlots _ _ _ (by decide)]
    all_goals rw [afterPower,install_other powerSlots _ _ _ (by decide)]
    all_goals rw [templated,install_other templateSlots _ _ _ (by decide)]
    all_goals rfl)
  have total:=ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ ht hpower) hliteral) hsum
  obtain ⟨r,hr,htapes,hheads,hsteps⟩:=total
  refine ⟨output n c d P,⟨r,hr,funext hheads,htapes,hsteps⟩,?_,?_⟩
  · rw [output,install_other sumSlots _ _ _ (by decide)]
    rw [afterLiteral,install_other literalSlots _ _ _ (by decide)]
    rw [afterPower,install_other powerSlots _ _ _ (by decide)]
    exact install_slot templateSlots template_inj _ _ 0
  · exact install_slot sumSlots sum_inj _ _ 2

end Completion.UnaryAffine
