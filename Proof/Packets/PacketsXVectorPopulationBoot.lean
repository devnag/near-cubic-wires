import Proof.Packets.PacketsXVectorDriverBoot
import Proof.Packets.UnaryHalf

/-! The provider's literal population is twice the original population.
A paid unary halving generates the actual vector population master before
constructing the child and parent drivers. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def populationSlots : Fin 3→Fin 299 := ![184,281,282]
def populationMachine := RecoveryFocus.machine populationSlots UnaryHalf.returned
def populationData (R M : Nat) (A : Fin 299→List Bool) :=
  Function.update A 281 (ZeroPadding.pad R (CompareMachine.word M))
def initializeDrivers := Composition.machine populationMachine bootDrivers

theorem population_run (R M : Nat) (A : Fin 299→List Bool)
    (hliteral : A 184=ZeroPadding.pad R (CompareMachine.word (2*M)))
    (hout : A 281=List.replicate R false) (hlog : A 282=List.replicate R false)
    (hr : 2*M+2≤R) :
    Step populationMachine (4*M+6) heads A heads (populationData R M A) := by
  have h:=UnaryHalf.ready R (2*M) hr
  have hd : 2*M/2=M := by omega
  have hf : 2*(2*M)+6=4*M+6 := by omega
  rw [hf] at h
  apply PhysicalFocusBoundary.focus h populationSlots (by decide) heads heads A (populationData R M A)
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j
    · exact hliteral.symm
    · simpa [UnaryHalf.padded,UnaryHalf.input,ZeroPadding.pad,Fin.addCases,populationSlots] using hout.symm
    · exact hlog.symm
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j
    · simpa [UnaryHalf.padded,UnaryHalf.data,Fin.addCases,populationSlots,populationData,Function.update] using hliteral.symm
    · simp [UnaryHalf.padded,UnaryHalf.data,Fin.addCases,populationData,Function.update,populationSlots,hd]
    · simpa [UnaryHalf.padded,UnaryHalf.data,Fin.addCases,populationSlots,populationData,Function.update] using hlog.symm
  · intro i away
    have hn : i≠281 := by intro he;exact away 1 he.symm
    exact ⟨rfl,by simp only [populationData,Function.update_of_ne hn]⟩

theorem initialize_drivers_run (R M depth : Nat) (A : Fin 299→List Bool)
    (hR : A 31=UnaryTemplate.tape R)
    (hM : A 184=ZeroPadding.pad R (CompareMachine.word (2*M)))
    (hD : A 260=ZeroPadding.pad R (CompareMachine.word depth))
    (hm : 2*M+2≤R) (hd : depth+1≤R)
    (h281 : A 281=List.replicate R false) (h282 : A 282=List.replicate R false)
    (h296 : (A 296).length=R) (h297 : (A 297).length=R) (h298 : (A 298).length=R) :
    Step initializeDrivers (6*R+8*M+37) heads A heads
      (driverData R M depth (populationData R M A)) := by
  have first:=population_run R M A hM h281 h282 hm
  have last:=drivers_run R M depth (populationData R M A)
    (by simpa [populationData,Function.update] using hR) (by simp [populationData])
    (by simpa [populationData,Function.update] using hD) (by omega) hd
    (by simpa [populationData,Function.update] using h296)
    (by simpa [populationData,Function.update] using h297)
    (by simpa [populationData,Function.update] using h298)
  have whole:=first.seq last
  have hf : (4*M+6)+1+(6*R+4*M+30)=6*R+8*M+37 := by omega
  rw [hf] at whole;exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
