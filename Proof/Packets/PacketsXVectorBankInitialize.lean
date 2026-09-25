import Proof.Packets.PacketsXVectorTerminalDock

/-! Both resident vector banks are physically initialized before the depth
loop: terminal one/zeros in the previous bank and zeros in the next bank. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] PhysicalZeroBank.machine terminalPrevious

def nextSlots : Fin 4→Fin 299 := ![31,257,263,297]
def initializeNext := RecoveryFocus.machine nextSlots PhysicalZeroBank.machine
def initializeVectors := Composition.machine terminalPrevious initializeNext

theorem initialize_next_run (R M : Nat) (A : Fin 299→List Bool)
    (h31 : A 31=UnaryTemplate.tape R) (h257 : A 257=[])
    (h263 : A 263=List.replicate R false)
    (h297 : A 297=ZeroPadding.pad R (CompareMachine.word (M+1))) :
    Step initializeNext (PhysicalZeroBank.budget R (M+1)) heads A heads
      (Function.update A 257 (List.replicate ((M+1)*(2*R)) false)) := by
  have small:=(PhysicalZeroBank.run R (M+1)).pad (![0,0,R,R] : Fin 4→Nat)
  apply PhysicalFocusBoundary.focus small nextSlots (by decide) heads heads A _
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>simp [nextSlots,PhysicalZeroBank.tapes,ZeroPadding.pad_zero,
      ZeroPadding.pad,h31,h257,h263,h297]
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>simp [nextSlots,PhysicalZeroBank.tapes,ZeroPadding.pad_zero,
      ZeroPadding.pad,h31,h257,h263,h297]
  · intro i away
    have hi:i≠257 := by intro he;exact away 1 he.symm
    exact ⟨rfl,by simp only [Function.update_of_ne hi]⟩

theorem initialize_vectors_run (R C M : Nat) (A : Fin 299→List Bool) (hC : C≤R) (hR : 2≤R)
    (hin : ∀j,A (terminalSlots j)=ZeroPadding.pad (terminalCaps R j)
      (VectorTerminalBank.A R C M [] (List.replicate R false) (List.replicate R false) j))
    (h257 : A 257=[]) (h297 : A 297=ZeroPadding.pad R (CompareMachine.word (M+1))) :
    Step initializeVectors (VectorTerminalBank.budget R C M+PhysicalZeroBank.budget R (M+1)+7)
      heads A heads
      (Function.update (terminalOutput R C M A) 257 (List.replicate ((M+1)*(2*R)) false)) := by
  have first:=terminal_previous_run R C M A hC hR hin
  have h31 : A 31=UnaryTemplate.tape R := by simpa [terminalSlots,terminalCaps,VectorTerminalBank.A] using hin 0
  have h263 : A 263=List.replicate R false := by simpa [terminalSlots,terminalCaps,VectorTerminalBank.A,ZeroPadding.pad] using hin 2
  have last:=initialize_next_run R M (terminalOutput R C M A)
    (by simpa [terminalOutput,Function.update] using h31)
    (by simpa [terminalOutput,Function.update] using h257)
    (by simpa [terminalOutput,Function.update] using h263)
    (by simpa [terminalOutput,Function.update] using h297)
  have whole:=first.seq last
  have hf : (VectorTerminalBank.budget R C M+6)+1+PhysicalZeroBank.budget R (M+1)=
      VectorTerminalBank.budget R C M+PhysicalZeroBank.budget R (M+1)+7 := by omega
  rw [hf] at whole
  exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
