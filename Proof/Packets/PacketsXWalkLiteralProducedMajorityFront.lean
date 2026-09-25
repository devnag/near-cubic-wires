import Proof.Packets.PacketsXWalkLiteralProducedMajoritySource

/-! Allocate the initially empty candidate tape, then physically derive all
sample scalar metadata before touching the first column destination. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section
attribute [local irreducible] MajorityComplete.Cold.lower MajorityComplete.Cold.scalar

def zeroWords (S : Nat) : Fin 3→List Bool := ![List.replicate S false,List.replicate S true,List.replicate (S+1) false]
def zeroBank (S : Nat) (A : Fin 742→List Bool) := install zeroSlots A (zeroWords S)
def scalarHeads (H : Fin 742→Nat) := dockH coldSlots H (fun _=>0)
def scalarBank (C R n : Nat) (A : Fin 742→List Bool) :=
  install coldSlots A (MajorityComplete.Cold.afterScalar C R n [])
def metadataHeads : Fin 5→Nat := ![0,0,0,0,1]

theorem zero_small (S : Nat) : Step (NativeFanout.machine zeroSelect) (2*S+4)
    (fun _=>0) (![[],List.replicate S true,[]] : Fin 3→List Bool) (fun _=>0) (zeroWords S) := by
  have h:=Step.of_ready (NativeFanout.ready zeroSelect (fun i : Fin 0=>i.elim0) S (fun i=>i.elim0))
  have hin : NativeFanout.input (m:=1) (fun i : Fin 0=>i.elim0) S=(![[],List.replicate S true,[]] : Fin 3→List Bool) := by
    funext i;fin_cases i <;>rfl
  have hout : NativeFanout.output zeroSelect (fun i : Fin 0=>i.elim0) S=zeroWords S := by
    funext i;fin_cases i <;>simp [NativeFanout.output,NativeFanout.word,zeroSelect,zeroWords,ZeroPadding.pad,Fin.addCases]
  exact (h.congr_in rfl hin).congr rfl hout

theorem zero_run (S : Nat) (H : Fin 742→Nat) (A : Fin 742→List Bool)
    (hh : ∀i,H (zeroSlots i)=0) (hs : A 424=List.replicate S true)
    (ht : A 567=[]) (hl : A 741=[]) :
    Step zeroMachine (2*S+4) H A H (zeroBank S A) := by
  have ha : ∀i,A (zeroSlots i)=(![[],List.replicate S true,[]] : Fin 3→List Bool) i := by
    intro i;fin_cases i
    · exact ht
    · exact hs
    · exact hl
  have h:=SourceDock.dock (zero_small S) zeroSlots (by decide) H A hh ha
  exact h.congr (SourceDock.heads_existing zeroSlots H (fun _=>0) hh) rfl

theorem scalar_front_run (C R n : Nat) (H : Fin 742→Nat) (A : Fin 742→List Bool)
    (hh : ∀i,H (coldSlots i)=MajorityComplete.Cold.inputHeads metadataHeads i)
    (ha : ∀i,A (coldSlots i)=MajorityComplete.Cold.input C R n [] i) :
    Step scalarFront (2+MajorityScalarProducer.budget n) H A (scalarHeads H) (scalarBank C R n A) := by
  have h:= (MajorityComplete.Cold.lower_run C R n [] metadataHeads (by intro i;fin_cases i <;>decide)).seq
    (MajorityComplete.Cold.scalar_run C R n [])
  exact SourceDock.dock h coldSlots cold_injective H A hh ha

def front := Composition.machine zeroMachine scalarFront
def frontBudget (S n : Nat) := 2*S+7+MajorityScalarProducer.budget n

theorem front_run (C R S n : Nat) (H : Fin 742→Nat) (A : Fin 742→List Bool)
    (hz : ∀i,H (zeroSlots i)=0) (hs : A 424=List.replicate S true)
    (ht : A 567=[]) (hl : A 741=[])
    (hh : ∀i,H (coldSlots i)=MajorityComplete.Cold.inputHeads metadataHeads i)
    (ha : ∀i,A (coldSlots i)=MajorityComplete.Cold.input C R n [] i) :
    Step front (frontBudget S n) H A (scalarHeads H) (scalarBank C R n (zeroBank S A)) := by
  have prep:=zero_run S H A hz hs ht hl
  have pin : ∀i,zeroBank S A (coldSlots i)=MajorityComplete.Cold.input C R n [] i := by
    intro i
    rw [zeroBank,install_other _ _ _ _ (fun j=>zero_cold_disjoint j i)]
    exact ha i
  have last:=scalar_front_run C R n H (zeroBank S A) hh pin
  simpa only [front,frontBudget,show 2*S+4+1+(2+MajorityScalarProducer.budget n)=2*S+7+MajorityScalarProducer.budget n by omega]
    using prep.seq last

end
end Theorem25Completion.WalkLiteralProducedMajority
