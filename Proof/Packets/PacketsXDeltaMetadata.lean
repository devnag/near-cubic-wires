import Proof.Packets.DeltaScalarFields
import Proof.Packets.PacketsXDeltaTargetGuard

/-! An executed complete delta metadata calculation. Retained unary masters
are split and framed physically; subtraction and both validity flags are
then computed on the resulting framed operands. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DeltaMetadata
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open RecoveryRootRound SignedSortKey DeltaScalarFields
noncomputable section

def slots : Fin 15→Fin 25 := ![8,9,10,14,15,16,17,18,19,20,21,22,12,23,24]
def guard := RecoveryFocus.machine slots DeltaTargetGuard.machine
def machine := Composition.machine DeltaScalarFields.machine guard
def budget (u n w parent child : Nat) := DeltaScalarFields.budget u n w parent child+1+DeltaTargetGuard.budget u

theorem pad_nil (R : Nat) : ZeroPadding.pad R []=List.replicate R false := by simp [ZeroPadding.pad]

theorem pad_false (R : Nat) : ZeroPadding.pad R (List.replicate R false)=List.replicate R false := by
  simp [ZeroPadding.pad]

theorem run (R u n w parent child : Nat)
    (hn : n<2^u) (hsum : min n w+parent<2^u) (hc : 2*child<2^u) (hw : 2*w<2^u)
    (hR : DeltaTargetGuard.budget u+1≤R) (hN : n+2≤R) :
    ∃ T,Step machine (budget u n w parent child) heads (input R u n w parent child) heads T ∧
      (∀i,i≤7→T i=splitData R u n w parent child i) ∧
      T 11=fw R u (n-w) ∧ T 12=fw R u (2*w) ∧
      T 19=ZeroPadding.pad R [decide (2*child≤ min n w+parent)] ∧
      T 21=fw R u (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)) ∧
      T 23=ZeroPadding.pad R [decide (CompetitorSignedResidue.residue u u (min n w+parent) (2*child)≤2*w)] ∧
      (∀i,(∃j,slots j=i)→(T i).length=R) := by
  have hu : 2*u+1≤R := by unfold DeltaTargetGuard.budget at hR;omega
  have fields:=DeltaScalarFields.run R u n w parent child hn (by omega) (by omega) hw hu hN
  obtain ⟨B,hb,hbl,b0,b1,b2,b8,b10,b12,b13⟩:=DeltaTargetGuard.padded_run u (min n w) parent child (2*w) R hsum hc hw hR
  let A:=converted5 R u n w parent child
  have matchInput : ∀ j, A (slots j)=ZeroPadding.pad R
      (DeltaTargetGuard.input u (min n w) parent child (2*w) R j) := by
    intro j;fin_cases j <;>
      simp [A,converted5,converted4,converted3,converted2,converted1,start,
        seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,
        slots,Function.update,DeltaTargetGuard.input,DeltaTargetGuard.extras,
        C10ThresholdOneHotTargetArithmetic.input,Fin.addCases,pad_false,pad_nil]
  have last:=hb.dock slots (by decide) heads A
    (by intro j;fin_cases j <;>rfl) matchInput
  rw [dockH_existing slots heads (fun _=>0) (by intro j;fin_cases j <;>rfl)] at last
  have whole:=fields.seq last
  refine ⟨install slots A B,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have away : ∀j,slots j≠i := by intro j;fin_cases j <;> dsimp [slots] <;>omega
    rw [install_other slots A B i away]
    dsimp only [A,converted5,converted4,converted3,converted2,converted1,start,
      seedData5,seedData4,seedData3,seedData2,seedData1]
    simp only [Function.update_of_ne (show i≠8 by omega),Function.update_of_ne (show i≠9 by omega),
      Function.update_of_ne (show i≠10 by omega),Function.update_of_ne (show i≠11 by omega),
      Function.update_of_ne (show i≠12 by omega)]
  · rw [install_other slots A B 11 (by decide)]
    simp [A,converted5,converted4,fw,Function.update]
  · exact (install_slot slots (by decide) A B 12).trans b12
  · exact (install_slot slots (by decide) A B 8).trans b8
  · exact (install_slot slots (by decide) A B 10).trans b10
  · exact (install_slot slots (by decide) A B 13).trans b13
  · intro i ⟨j,hj⟩
    subst i
    rw [install_slot slots (by decide) A B j]
    exact hbl j

end
end PCJ9eff70d512234a4c_Fixed.Materializer.DeltaMetadata
