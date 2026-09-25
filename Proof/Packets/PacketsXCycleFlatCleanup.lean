import Proof.Packets.PacketsXCycleFlatSerialize

/-! Reusable eight-tape final-packet adapter. It serializes the already
computed monomials in their exact order, appends to the family stream, and
physically restores every work tape to its common zero reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleFlatSerialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed
noncomputable section

def workCaps (R : Nat) : Fin 5→Nat := ![0,R,R,0,R]
def selected (i : Fin 5) : Bool := decide (i≠3)
def resetMachine := MaskedReset.machine machine selected
def first := TapeEmbedding.machine 2 resetMachine
def scratchSlots : Fin 4→Fin 8 := ![1,2,4,5]
def eraseSlots : Fin 6→Fin 8 := ![1,2,4,5,6,7]
theorem erase_injective : Function.Injective eraseSlots := by decide
def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 4)
def transaction := Composition.machine first last
def transactionBudget (B R : Nat) (rows : List (List Bool)) := 2*budget B rows+2*R+7

variable (B R : Nat) (rows : List (List Bool)) (out : List Bool)
def paddedInput := fun i=>ZeroPadding.pad (workCaps R i) (input B R rows out i)
def paddedOutput := fun i=>ZeroPadding.pad (workCaps R i) (output B R rows out i)
def input6 : Fin 6→List Bool := Fin.addCases (m:=5) (n:=1) (paddedInput B R rows out)
  (fun _=>List.replicate R false)
def output6 : Fin 6→List Bool := Fin.addCases (m:=5) (n:=1) (paddedOutput B R rows out)
  (fun _=>List.replicate R false)
def heads6 (out : List Bool) : Fin 6→Nat := ![0,0,0,out.length,0,0]
def transactionInput : Fin 8→List Bool := Fin.addCases (m:=6) (n:=2) (input6 B R rows out)
  (![List.replicate R true,List.replicate (R+1) false])
def middle : Fin 8→List Bool := Fin.addCases (m:=6) (n:=2) (output6 B R rows out)
  (![List.replicate R true,List.replicate (R+1) false])
def transactionHeads (out : List Bool) : Fin 8→Nat := ![0,0,0,out.length,0,0,0,0]
def backing (i : Fin 4) := middle B R rows out (scratchSlots i)
def eraseInput : Fin 6→List Bool :=
  Fin.addCases (m:=5) (n:=1)
    (Fin.addCases (m:=4) (n:=1) (backing B R rows out) (fun _=>List.replicate R true))
    (fun _=>List.replicate (R+1) false)
def eraseOutput (R : Nat) : Fin 6→List Bool :=
  ![List.replicate R false,List.replicate R false,List.replicate R false,List.replicate R false,
    List.replicate R true,List.replicate (R+1) false]
def transactionOutput := install eraseSlots (middle B R rows out) (eraseOutput R)
def cleanBank (B R : Nat) (out : List Bool) : Fin 8→List Bool :=
  ![UnaryTemplate.tape B,List.replicate R false,List.replicate R false,out,
    List.replicate R false,List.replicate R false,List.replicate R true,List.replicate (R+1) false]

theorem flatten_length (hw : ∀ row∈rows,row.length=B) : rows.flatten.length=rows.length*B := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hrow := hw row (by simp)
    have hrest : ∀ r∈rows,r.length=B := fun r hr=>hw r (by simp [hr])
    simp [List.flatten_cons,hrow,ih hrest,Nat.add_mul,Nat.add_comm]

theorem input_fits (hR : budget B rows+1≤R) (hw : ∀ row∈rows,row.length=B)
    (i : Fin 5) (hi0 : i≠0) (hi3 : i≠3) : (paddedInput B R rows out i).length≤R := by
  have hflat := flatten_length B rows hw
  have hmult := Nat.mul_le_mul_left rows.length (show B≤B^2+8*B+9 by omega)
  have hcount := Nat.mul_le_mul_left rows.length (show 1≤B^2+8*B+9 by omega)
  unfold budget at hR
  fin_cases i
  · exact False.elim (hi0 rfl)
  · simp only [paddedInput,workCaps,input,ZeroPadding.pad_length]
    apply max_le le_rfl
    change rows.flatten.length≤R
    omega
  · change (ZeroPadding.pad R (List.replicate R false)).length≤R
    simp [ZeroPadding.pad_length]
  · exact False.elim (hi3 rfl)
  · change (ZeroPadding.pad R (CompareMachine.word rows.length)).length≤R
    rw [ZeroPadding.pad_length]
    apply max_le le_rfl
    simp only [CompareMachine.word,List.length_cons,List.length_replicate]
    omega

theorem output_fits (hB : B+3≤R) (hR : budget B rows+1≤R)
    (hw : ∀ row∈rows,row.length=B) (i : Fin 5) (hi0 : i≠0) (hi3 : i≠3) :
    (paddedOutput B R rows out i).length≤R := by
  obtain ⟨r,hr,_,ht,hs⟩ := (run B R rows out hB hw).pad (workCaps R)
  have hh : heads out i≤0 := by fin_cases i <;>first | exact False.elim (hi3 rfl) | rfl
  have h := PCPSerializerReuse.tape_support machine _ _ r hr i R 0 hh
    ((input_fits B R rows out hR hw i hi0 hi3).trans (Nat.le_max_left _ _))
  rw [ht] at h
  exact h.trans (max_le le_rfl (by omega))

theorem reset_run (hB : B+3≤R) (hR : budget B rows≤R) (hw : ∀ row∈rows,row.length=B) :
    Step resetMachine (2*budget B rows+2) (heads6 out) (input6 B R rows out)
      (heads6 (out++word rows)) (output6 B R rows out) := by
  have h := ((run B R rows out hB hw).pad (workCaps R)).mask selected
    (by intro i hi;fin_cases i <;>simp [selected,heads] at hi ⊢) hR
  apply (h.congr_in ?_ rfl).congr ?_ rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>rfl

theorem first_run (hB : B+3≤R) (hR : budget B rows≤R) (hw : ∀ row∈rows,row.length=B) :
    Step first (2*budget B rows+2) (transactionHeads out) (transactionInput B R rows out)
      (transactionHeads (out++word rows)) (middle B R rows out) := by
  have h := (reset_run B R rows out hB hR hw).embed (fun _ : Fin 2=>0)
    (![List.replicate R true,List.replicate (R+1) false])
  apply (h.congr_in ?_ rfl).congr ?_ rfl
  all_goals funext i;fin_cases i <;>rfl

theorem backing_fits (hB : B+3≤R) (hR : budget B rows+1≤R) (hw : ∀ row∈rows,row.length=B) :
    ∀ i,(backing B R rows out i).length≤R := by
  intro i;fin_cases i
  · exact output_fits B R rows out hB hR hw 1 (by decide) (by decide)
  · exact output_fits B R rows out hB hR hw 2 (by decide) (by decide)
  · exact output_fits B R rows out hB hR hw 4 (by decide) (by decide)
  · change (List.replicate R false).length≤R;simp

theorem last_run (hB : B+3≤R) (hR : budget B rows+1≤R) (hw : ∀ row∈rows,row.length=B) :
    Step last (2*R+4) (transactionHeads (out++word rows)) (middle B R rows out)
      (transactionHeads (out++word rows)) (transactionOutput B R rows out) := by
  have h := Step.of_ready (RecoveryScratchErase.erase_ready R (R+1) (backing B R rows out)
    (backing_fits B R rows out hB hR hw))
  rw [max_self] at h
  have hh : ∀ j,transactionHeads (out++word rows) (eraseSlots j)=0 := by intro j;fin_cases j <;>rfl
  have ht : ∀ j,middle B R rows out (eraseSlots j)=eraseInput B R rows out j := by intro j;fin_cases j <;>rfl
  have hf := CycleNormalize.dock_step h eraseSlots erase_injective _ _ hh ht
  apply hf.congr (CycleNormalize.dock_existing _ _ _ hh) ?_
  apply congrArg (install eraseSlots (middle B R rows out))
  funext i;fin_cases i <;>rfl

theorem clean_output : transactionOutput B R rows out=cleanBank B R (out++word rows) := by
  funext i;fin_cases i
  · rw [transactionOutput,install_other _ _ _ _ (by decide)]
    change ZeroPadding.pad 0 (ZeroPadding.pad 0 (UnaryTemplate.tape B))=_
    simp only [ZeroPadding.pad_zero]
    rfl
  · exact install_slot eraseSlots erase_injective _ _ 0
  · exact install_slot eraseSlots erase_injective _ _ 1
  · rw [transactionOutput,install_other _ _ _ _ (by decide)]
    change ZeroPadding.pad 0 (output B R rows out 3)=_
    rw [ZeroPadding.pad_zero,output_word]
    rfl
  · exact install_slot eraseSlots erase_injective _ _ 2
  · exact install_slot eraseSlots erase_injective _ _ 3
  · exact install_slot eraseSlots erase_injective _ _ 4
  · exact install_slot eraseSlots erase_injective _ _ 5

/-- One actual reusable transaction preserves the exact input monomial order
and returns all four scratch tapes to their original zero reserve. -/
theorem transaction_run (hB : B+3≤R) (hR : budget B rows+1≤R) (hw : ∀ row∈rows,row.length=B) :
    Step transaction (transactionBudget B R rows) (transactionHeads out) (transactionInput B R rows out)
      (transactionHeads (out++word rows)) (cleanBank B R (out++word rows)) := by
  have h := (first_run B R rows out hB (by omega) hw).seq (last_run B R rows out hB hR hw)
  have ht : 2*budget B rows+2+1+(2*R+4)=transactionBudget B R rows := by unfold transactionBudget;omega
  rw [ht] at h
  exact h.congr rfl (clean_output B R rows out)

end
end Theorem25Completion.CycleFlatSerialize
