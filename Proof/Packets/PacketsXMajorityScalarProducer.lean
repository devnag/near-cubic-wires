import Proof.Packets.PacketsXMajorityScalarNumeric
import Proof.Packets.MajorityScalarOne

/-! All sample-dependent majority scalar masters, computed from the actual
retained Compare n word. N=n+1 is the number of walk visits. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Completion.MajorityScalarProducer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Theorem25Completion
noncomputable section

def input (n : Nat) : Fin 30→List Bool:=
  Fin.addCases (m:=10) (n:=20) (motive:=fun _=>List Bool)
    (MajorityScalarNumeric.input n) (fun _=>[])
def numericBank (n k : Nat) : Fin 30→List Bool:=
  Fin.addCases (m:=10) (n:=20) (motive:=fun _=>List Bool)
    (MajorityScalarNumeric.thresholdBank n k) (fun _=>[])
def powerSlots : Fin 21→Fin 30:=![1,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
def oneSlot : Fin 1→Fin 30:=fun _=>9
def numericMachine:=TapeEmbedding.machine 20 MajorityScalarNumeric.machine
def powerMachine:=RecoveryFocus.machine powerSlots MajorityScalarSeed.powerMachine
def oneMachine:=RecoveryFocus.machine oneSlot MajorityScalarOne.machine
def machine:=Composition.machine (Composition.machine numericMachine powerMachine) oneMachine
def budget (n : Nat):=MajorityScalarNumeric.budget n+1+MajorityScalarSeed.powerBudget (n+1)+1+2

theorem zero_heads {t u : Nat} (slots : Fin t→Fin u) :
    dockH slots (fun _ : Fin u=>0) (fun _=>0)=(fun _=>0) := by
  funext i
  unfold dockH
  cases RecoveryFocus.pick slots i <;>rfl

theorem run (n : Nat) : ∃ out,
    Step machine (budget n) (fun _=>0) (input n) (fun _=>0) out ∧
    out 5=CompareMachine.word (n+1) ∧
    out 7=CompareMachine.word ((n+1+1)/2) ∧
    out 9=CompareMachine.word 1 ∧
    out 11=frame (SignedSortKey.binary (n+1) 0) ∧
    out 28=CompareMachine.word (2^(n+1)-1) ∧
    out 26=UnaryTemplate.tape (2^(n+1)) := by
  obtain ⟨k,_,hn⟩:=MajorityScalarNumeric.run n
  have numeric : Step numericMachine (MajorityScalarNumeric.budget n)
      (fun _=>0) (input n) (fun _=>0) (numericBank n k) := by
    have hz : Fin.addCases (m:=10) (n:=20) (motive:=fun _=>Nat)
        (fun _=>0) (fun _=>0)=(fun _ : Fin 30=>0) := by
      funext i
      refine Fin.addCases (m:=10) (n:=20) (fun j=>?_) (fun j=>?_) i <;>
        simp only [Fin.addCases_left,Fin.addCases_right]
    exact ((hn.embed (fun _ : Fin 20=>0) (fun _=>[])).congr_in hz rfl).congr hz rfl
  obtain ⟨p,hp,hpa,hpb,hpc⟩:=MajorityScalarSeed.power_run (n+1)
  have power:=hp.dock powerSlots (by decide) (fun _ : Fin 30=>0) (numericBank n k)
    (by intro i;rfl) (by intro i;fin_cases i <;>rfl)
  have power':Step powerMachine (MajorityScalarSeed.powerBudget (n+1))
      (fun _=>0) (numericBank n k) (fun _=>0) (install powerSlots (numericBank n k) p):=
    power.congr (zero_heads powerSlots) rfl
  let middle:=install powerSlots (numericBank n k) p
  have hm5 : middle 5=CompareMachine.word (n+1) :=
    install_other powerSlots _ _ 5 (by decide)
  have hm7 : middle 7=CompareMachine.word ((n+1+1)/2) :=
    install_other powerSlots _ _ 7 (by decide)
  have hm9 : middle 9=[]:=install_other powerSlots _ _ 9 (by decide)
  have hm11 : middle 11=frame (SignedSortKey.binary (n+1) 0):=
    (install_slot powerSlots (by decide) _ _ 2).trans hpa
  have hm28 : middle 28=CompareMachine.word (2^(n+1)-1):=
    (install_slot powerSlots (by decide) _ _ 19).trans hpb
  have hm26 : middle 26=UnaryTemplate.tape (2^(n+1)):=
    (install_slot powerSlots (by decide) _ _ 17).trans hpc
  have one:=MajorityScalarOne.run.dock oneSlot (by decide) (fun _ : Fin 30=>0) middle
    (by intro i;rfl) (by intro i;exact hm9)
  have one':Step oneMachine 2 (fun _=>0) middle (fun _=>0)
      (install oneSlot middle (fun _=>CompareMachine.word 1)):=
    one.congr (zero_heads oneSlot) rfl
  refine ⟨_,(numeric.seq power').seq one',?_,?_,?_,?_,?_,?_⟩
  · exact (install_other oneSlot _ _ 5 (by decide)).trans hm5
  · exact (install_other oneSlot _ _ 7 (by decide)).trans hm7
  · exact install_slot oneSlot (by decide) _ _ 0
  · exact (install_other oneSlot _ _ 11 (by decide)).trans hm11
  · exact (install_other oneSlot _ _ 28 (by decide)).trans hm28
  · exact (install_other oneSlot _ _ 26 (by decide)).trans hm26

end
end Completion.MajorityScalarProducer
