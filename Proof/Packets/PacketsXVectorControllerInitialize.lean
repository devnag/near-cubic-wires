import Proof.Packets.PacketsXVectorPhaseChange
import Proof.Packets.PacketsXVectorDepthMaster
import Proof.Packets.PacketsXVectorBankInitialize

/-! Closed physical initialization for the bottom-up controller. Source
population/depth are retained; all loop drivers and both vector banks are
constructed by execution before the first level. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] phaseChange depthMaster initializeDrivers populationMaster initializeVectors

def blankPorts : List (Fin 299) := [0,25,28,161,185,258,259,260,263,281,282,296,297,298]
def phaseOutput (R M : Nat) (A : Fin 299→List Bool) :=
  Function.update (Function.update A 184 (ZeroPadding.pad R (CompareMachine.word (2*M))))
    185 (ZeroPadding.pad R (CompareMachine.word (Completion.SourceDigitWidth.digitWidth (2*M))))
def bootOutput (R M depth : Nat) (A : Fin 299→List Bool) :=
  Function.update (driverData R M depth (populationData R M
    (Function.update (phaseOutput R M A) 260 (ZeroPadding.pad R (CompareMachine.word depth)))))
    161 (ZeroPadding.pad R (CompareMachine.word M))
def initialized (R C M depth : Nat) (A : Fin 299→List Bool) :=
  Function.update (terminalOutput R C M (bootOutput R M depth A)) 257
    (List.replicate ((M+1)*(2*R)) false)
def initializeController := Composition.machine phaseChange (Composition.machine depthMaster
  (Composition.machine initializeDrivers (Composition.machine populationMaster initializeVectors)))
def initializeBudget (R C M : Nat) := phaseBudget R M+10*R+8*M+56+
  VectorTerminalBank.budget R C M+PhysicalZeroBank.budget R (M+1)

theorem initialize_controller_run (R C M depth : Nat) (A : Fin 299→List Bool)
    (hC : C≤R) (hR : 2≤R) (hd : depth+1≤R)
    (hcap : Completion.SourceDigitWidth.capacity (2*M)≤R)
    (a31 : A 31=UnaryTemplate.tape R) (a32 : A 32=List.replicate R true)
    (a33 : A 33=List.replicate (R+3) false)
    (a24 : A 24=ZeroPadding.pad R (UnaryTemplate.tape C))
    (a177 : A 177=ZeroPadding.pad R (CompareMachine.word depth))
    (a184 : A 184=ZeroPadding.pad R (CompareMachine.word M))
    (a256 : A 256=[]) (a257 : A 257=[])
    (blank : ∀i,i∈blankPorts→A i=List.replicate R false)
    (work : ∀j,A (widthSlots j)=List.replicate R false) :
    Step initializeController (initializeBudget R C M) heads A heads (initialized R C M depth A) := by
  have hm : 2*M+2≤R := by unfold Completion.SourceDigitWidth.capacity at hcap;nlinarith
  have first:=phase_change_run R M A a31 (blank 0 (by decide)) a32 a33 a184 work
    (by rw [blank 185 (by decide),List.length_replicate]) hcap
  change Step phaseChange (phaseBudget R M) heads A heads (phaseOutput R M A) at first
  let A1:=phaseOutput R M A
  let A2:=Function.update A1 260 (ZeroPadding.pad R (CompareMachine.word depth))
  let A3:=driverData R M depth (populationData R M A2)
  let A4:=Function.update A3 161 (ZeroPadding.pad R (CompareMachine.word M))
  have second:=depth_master_run R depth A1
    (by simpa [A1,phaseOutput,Function.update] using a31)
    (by simpa [A1,phaseOutput,Function.update] using a177) hd
    (by simp [A1,phaseOutput,Function.update,blank 260 (by decide)])
  have third:=initialize_drivers_run R M depth A2
    (by simpa [A2,A1,phaseOutput,Function.update] using a31)
    (by simp [A2,A1,phaseOutput,Function.update]) (by simp [A2]) hm hd
    (by simpa [A2,A1,phaseOutput,Function.update] using blank 281 (by decide))
    (by simpa [A2,A1,phaseOutput,Function.update] using blank 282 (by decide))
    (by simp [A2,A1,phaseOutput,Function.update,blank 296 (by decide)])
    (by simp [A2,A1,phaseOutput,Function.update,blank 297 (by decide)])
    (by simp [A2,A1,phaseOutput,Function.update,blank 298 (by decide)])
  have fourth:=population_master_run R M A3
    (by simpa [A3,A2,A1,driverData,populationData,phaseOutput,Function.update] using a31)
    (by simp [A3,driverData,populationData,Function.update]) (by omega)
    (by simp [A3,A2,A1,driverData,populationData,phaseOutput,Function.update,blank 161 (by decide)])
  have inputs : ∀j,A4 (terminalSlots j)=ZeroPadding.pad (terminalCaps R j)
      (VectorTerminalBank.A R C M [] (List.replicate R false) (List.replicate R false) j) := by
    intro j;fin_cases j
    all_goals simp [A4,A3,A2,A1,terminalSlots,terminalCaps,VectorTerminalBank.A,driverData,populationData,
      phaseOutput,Function.update,a31,a24,a256,blank 25 (by decide),blank 28 (by decide),
      blank 263 (by decide),blank 258 (by decide)]
    · simp [ZeroPadding.pad]
    · exact (GradedWindow.zero_count R (by omega)).symm
  have last:=initialize_vectors_run R C M A4 hC hR inputs
    (by simpa [A4,A3,A2,A1,driverData,populationData,phaseOutput,Function.update] using a257)
    (by simp [A4,A3,driverData,Function.update])
  have all:=first.seq (second.seq (third.seq (fourth.seq last)))
  have fuel : phaseBudget R M+1+((2*R+6)+1+((6*R+8*M+37)+1+((2*R+2)+1+
      (VectorTerminalBank.budget R C M+PhysicalZeroBank.budget R (M+1)+7))))=initializeBudget R C M := by
    unfold initializeBudget;omega
  rw [fuel] at all
  exact all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
