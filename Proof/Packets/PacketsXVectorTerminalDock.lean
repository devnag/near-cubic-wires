import Proof.Packets.PacketsXVectorNumericArena
import Proof.Packets.VectorTerminalBank

/-! The actual terminal-bank initializer in the shared299-port controller.
Both bank allocations begin at empty logical banks and accept outer padding
for a retained physical capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] VectorTerminalBank.machine PhysicalZeroBank.machine

def terminalSlots : Fin 8→Fin 299 := ![31,256,263,296,24,25,28,258]
def terminalCaps (R : Nat) : Fin 8→Nat := ![0,0,R,R,R,0,0,R]
def terminalBody := RecoveryFocus.machine terminalSlots VectorTerminalBank.machine
def terminalHeads (cp : Nat) := Function.update (Function.update heads 24 1) 28 cp
def terminalOutput (R C M : Nat) (A : Fin 299→List Bool) :=
  Function.update (Function.update (Function.update A 256 (VectorTerminalBank.result R C M))
    25 (ZeroPadding.pad R (List.replicate C false))) 28 (ZeroPadding.pad R (CompareMachine.word 1))
def terminalPrevious := Composition.machine (PhysicalIndexReload.move (24 : Fin 299) .right)
  (Composition.machine terminalBody (Composition.machine
    (PhysicalIndexReload.move (24 : Fin 299) .left) (PhysicalIndexReload.move (28 : Fin 299) .left)))

theorem terminal_body_run (R C M : Nat) (A : Fin 299→List Bool) (hC : C≤R) (hR : 2≤R)
    (hin : ∀j,A (terminalSlots j)=ZeroPadding.pad (terminalCaps R j)
      (VectorTerminalBank.A R C M [] (List.replicate R false) (List.replicate R false) j)) :
    Step terminalBody (VectorTerminalBank.budget R C M) (terminalHeads 0) A
      (terminalHeads 1) (terminalOutput R C M A) := by
  have small:=(VectorTerminalBank.run R C M hC hR).pad (terminalCaps R)
  apply PhysicalFocusBoundary.focus small terminalSlots (by decide) (terminalHeads 0) (terminalHeads 1) A _
  · intro j;fin_cases j <;>rfl
  · exact fun j=>(hin j).symm
  · intro j;fin_cases j <;>rfl
  · intro j
    fin_cases j
    · exact (hin 0).symm
    · simp [terminalOutput,terminalSlots,terminalCaps,VectorTerminalBank.A]
    · exact (hin 2).symm
    · exact (hin 3).symm
    · exact (hin 4).symm
    · simp [terminalOutput,terminalSlots,terminalCaps,VectorTerminalBank.A]
    · simp [terminalOutput,terminalSlots,terminalCaps,VectorTerminalBank.A]
    · exact (hin 7).symm
  · intro i away
    have h256:i≠256 := by intro he;exact away 1 he.symm
    have h25:i≠25 := by intro he;exact away 5 he.symm
    have h28:i≠28 := by intro he;exact away 6 he.symm
    exact ⟨by simp only [terminalHeads,Function.update_of_ne h28],
      by simp only [terminalOutput,Function.update_of_ne h256,Function.update_of_ne h25,Function.update_of_ne h28]⟩

theorem terminal_previous_run (R C M : Nat) (A : Fin 299→List Bool) (hC : C≤R) (hR : 2≤R)
    (hin : ∀j,A (terminalSlots j)=ZeroPadding.pad (terminalCaps R j)
      (VectorTerminalBank.A R C M [] (List.replicate R false) (List.replicate R false) j)) :
    Step terminalPrevious (VectorTerminalBank.budget R C M+6) heads A heads (terminalOutput R C M A) := by
  have first:=PhysicalIndexReload.move_run (24 : Fin 299) .right heads A
  change Step _ 1 heads A (Function.update heads 24 1) A at first
  have middle:=terminal_body_run R C M A hC hR hin
  have he0 : terminalHeads 0=Function.update heads 24 1 := by
    unfold terminalHeads
    apply Function.update_eq_self_iff.mpr
    rfl
  rw [he0] at middle
  have third:=PhysicalIndexReload.move_run (24 : Fin 299) .left (terminalHeads 1) (terminalOutput R C M A)
  have last:=PhysicalIndexReload.move_run (28 : Fin 299) .left
    (Function.update (terminalHeads 1) 24 0) (terminalOutput R C M A)
  change Step _ 1 (terminalHeads 1) _ (Function.update (terminalHeads 1) 24 0) _ at third
  change Step _ 1 (Function.update (terminalHeads 1) 24 0) _
    (Function.update (Function.update (terminalHeads 1) 24 0) 28 0) _ at last
  have back : Function.update (Function.update (terminalHeads 1) 24 0) 28 0=heads := by
    funext i
    by_cases h24:i=24
    · subst i;rfl
    by_cases h28:i=28
    · subst i;rfl
    simp only [terminalHeads,Function.update_of_ne h24,Function.update_of_ne h28]
  have joined:=first.seq (middle.seq (third.seq (last.congr back rfl)))
  have hf : 1+1+(VectorTerminalBank.budget R C M+1+(1+1+1))=VectorTerminalBank.budget R C M+6 := by omega
  rw [hf] at joined
  exact joined

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
