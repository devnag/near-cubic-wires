import Proof.Rows.FinalNativeResidue

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueDriver
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Same preparation machine, with its actual width template and reusable
reverse log projected for the next physical consumer. -/
theorem prepare_run (pre tail : List Bool) (z : ℤ) (R : ℕ) (hR : 4*natBitLength z.natAbs+2≤R) :
    ∃ output : Fin 14 → List Bool,
      Step C10NativeResiduePrepare.machine (22*natBitLength z.natAbs+19)
        (C10NativeResiduePrepare.initialHeads pre.length)
        (C10NativeResiduePrepare.input (pre++intWord z++tail) R)
        (C10NativeResiduePrepare.heads (pre.length+(intWord z).length)) output ∧
      output 0=pre++intWord z++tail ∧ output 6=[decide (z<0)] ∧
      output 12=RecoveryRadixInput.prepared (SignedSortKey.binary (natBitLength z.natAbs) z.natAbs) ∧
      output 3=UnaryTemplate.tape (natBitLength z.natAbs) ∧ output 11=List.replicate R false := by
  let bits := SignedSortKey.binary (natBitLength z.natAbs) z.natAbs
  let source := pre++intWord z++tail
  let pos := pre.length+(intWord z).length
  let A : Fin 14 → List Bool := Fin.addCases (motive := fun _=>List Bool)
    (DecompositionNativeMagnitude.fieldOutput source pos bits (decide (z<0))).tapes
    (C10NativeResiduePrepare.extras R)
  have raw := (C10NativeResidueInput.field_step pre tail z).embed (fun _ : Fin 5=>0)
    (C10NativeResiduePrepare.extras R)
  have first : Step C10NativeResiduePrepare.first (6*natBitLength z.natAbs+9)
      (C10NativeResiduePrepare.initialHeads pre.length) (C10NativeResiduePrepare.input source R)
      (C10NativeResiduePrepare.heads pos) A := by
    refine (raw.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i; fin_cases i <;> rfl
  have hb : bits.length=natBitLength z.natAbs := SignedSortKey.binary_length _ _
  have ready := C10NativeResidueInput.prepare_unwrap bits R (by rw [hb]; exact hR)
  have second := (ready.dock C10NativeResiduePrepare.slots (by decide)
    (C10NativeResiduePrepare.heads pos) A
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)).congr
      (dockH_existing C10NativeResiduePrepare.slots _ _ (by intro j; fin_cases j <;> rfl)) rfl
  have total := first.seq second
  rw [hb] at total
  have ht : 6*natBitLength z.natAbs+9+1+(16*natBitLength z.natAbs+9)=22*natBitLength z.natAbs+19 := by omega
  rw [ht] at total
  refine ⟨_,total,?_,?_,?_,?_,?_⟩
  · exact (install_other C10NativeResiduePrepare.slots _ _ _ (by decide)).trans rfl
  · exact (install_other C10NativeResiduePrepare.slots _ _ _ (by decide)).trans rfl
  · exact install_slot C10NativeResiduePrepare.slots (by decide) _ _ 4
  · exact (install_other C10NativeResiduePrepare.slots _ _ (3 : Fin 14) (by decide)).trans
      (congrArg UnaryTemplate.tape hb)
  · exact install_slot C10NativeResiduePrepare.slots (by decide) _ _ 3

def retreat : Fin 3 → HeadMove := ![.left,.stay,.stay]
def advance : Fin 3 → HeadMove := ![.stay,.right,.stay]
noncomputable def machine := Composition.machine
  (Composition.machine (DecompositionCountPosition.move retreat) RecoveryColdView.doubleMachine)
  (DecompositionCountPosition.move advance)

def input (B F R : ℕ) : Fin 3 → List Bool :=
  ![ZeroPadding.pad F (UnaryTemplate.tape B),List.replicate F false,List.replicate R false]
def output (B F R : ℕ) : Fin 3 → List Bool :=
  ![ZeroPadding.pad F (UnaryTemplate.tape B),ZeroPadding.pad F (CompareMachine.word (2*B)),List.replicate R false]

theorem driver_run (B F R : ℕ) (hF : 2*B+2≤F) (hR : 2*B+2≤R) :
    Step machine (4*B+10) (![1,0,0] : Fin 3 → ℕ) (input B F R)
      (![0,1,0] : Fin 3 → ℕ) (output B F R) := by
  have base := Step.of_ready (RecoveryColdView.double_ready B R)
  rw [max_eq_left hR] at base
  have padded := base.pad (![F,F,0] : Fin 3 → ℕ)
  have doubled : Step RecoveryColdView.doubleMachine (4*B+6) (fun _=>0) (input B F R)
      (fun _=>0) (output B F R) := by
    refine (padded.congr_in rfl ?_).congr rfl ?_
    all_goals funext i; fin_cases i
    all_goals first
      | exact pad_template F B (by omega)
      | exact ZeroPadding.pad_zero _
      | rfl
  obtain ⟨a,ar,af,_⟩ := DecompositionCountPosition.move_run retreat (![1,0,0] : Fin 3 → ℕ) (input B F R)
  have first := (Step.of_run ar (congrArg Configuration.heads af) (congrArg Configuration.tapes af)).congr
    (show _=(fun _ : Fin 3=>0) by funext i; fin_cases i <;> rfl) rfl
  obtain ⟨c,cr,cf,_⟩ := DecompositionCountPosition.move_run advance (fun _ : Fin 3=>0) (output B F R)
  have last := (Step.of_run cr (congrArg Configuration.heads cf) (congrArg Configuration.tapes cf)).congr
    (show _=(![0,1,0] : Fin 3 → ℕ) by funext i; fin_cases i <;> rfl) rfl
  have whole := (first.seq doubled).seq last
  simpa only [machine, show 1+1+(4*B+6)+1+1=4*B+10 by omega] using whole

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueDriver
