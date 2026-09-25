import Proof.Packets.PacketsXVectorControllerInitialize

/-! Physical dense atom-bank allocation in the fixed 299-tape arena. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def denseSlots : Fin 4 → Fin 299 := ![31,140,263,24]
def allocateDense := RecoveryFocus.machine denseSlots PhysicalZeroBank.machine
def initializeDense := Composition.machine (PhysicalIndexReload.move (24 : Fin 299) .right)
  (Composition.machine allocateDense (PhysicalIndexReload.move (24 : Fin 299) .left))
def denseBudget (R C : Nat) := PhysicalZeroBank.budget R C+4
attribute [local irreducible] PhysicalZeroBank.machine

theorem initialize_dense_run (R C : Nat) (tapes : Fin 299 → List Bool) (hC : C+2≤R)
    (h31 : tapes 31=UnaryTemplate.tape R) (h24 : tapes 24=ZeroPadding.pad R (UnaryTemplate.tape C))
    (h140 : tapes 140=[]) (h263 : tapes 263=List.replicate R false) :
    Step initializeDense (denseBudget R C) heads tapes heads
      (Function.update tapes 140 (PacketVector.bank R (List.replicate C []))) := by
  let raised:=Function.update heads 24 1
  have up:=PhysicalIndexReload.move_run (24 : Fin 299) .right heads tapes
  change Step _ 1 heads tapes raised tapes at up
  have small:=(PhysicalZeroBank.run R C).pad (![0,0,R,R] : Fin 4 → Nat)
  have hw : tapes 24=ZeroPadding.pad R (CompareMachine.word C) :=
    h24.trans (VectorCounter.padded_template_word C R hC)
  have body : Step allocateDense (PhysicalZeroBank.budget R C) raised tapes raised
      (Function.update tapes 140 (List.replicate (C*(2*R)) false)) := by
    apply PhysicalFocusBoundary.focus small denseSlots (by decide) raised raised tapes _
    · intro j;fin_cases j <;>rfl
    · intro j;fin_cases j <;>simp [denseSlots,PhysicalZeroBank.tapes,ZeroPadding.pad_zero,
        ZeroPadding.pad,h31,hw,h140,h263]
    · intro j;fin_cases j <;>rfl
    · intro j;fin_cases j <;>simp [denseSlots,PhysicalZeroBank.tapes,ZeroPadding.pad_zero,
        ZeroPadding.pad,h31,hw,h140,h263]
    · intro i away
      have hn : i≠140 := by intro he;exact away 1 he.symm
      exact ⟨rfl,by simp only [Function.update_of_ne hn]⟩
  have down:=PhysicalIndexReload.move_run (24 : Fin 299) .left raised
    (Function.update tapes 140 (List.replicate (C*(2*R)) false))
  have back : Function.update raised 24 0=heads := by
    funext i
    by_cases hi : i=24
    · subst i;rfl
    · simp [raised,Function.update,hi]
  change Step _ 1 raised _ (Function.update raised 24 0) _ at down
  have all:=up.seq (body.seq (down.congr back rfl))
  have fuel : 1+1+(PhysicalZeroBank.budget R C+1+1)=denseBudget R C := by unfold denseBudget;omega
  rw [fuel] at all
  rw [VectorTerminalBank.empty_bank R C (by omega)]
  exact all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
