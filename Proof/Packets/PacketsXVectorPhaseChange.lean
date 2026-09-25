import Proof.Packets.PacketsXVectorPhaseDouble
import Proof.Packets.PacketsXVectorPhaseWidth

/-! Closed terminal-to-delta metadata phase change. Only the literal count
and its logarithmic subset width change; all working tapes are returned. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def phaseChange := Composition.machine phaseDouble regenerateWidth
def phaseBudget (R M : Nat) := 8*R+4*M+UnaryAddCount.budget M M+Completion.SourceDigitWidth.budget (2*M)+30

theorem phase_change_run (R M : Nat) (A : Fin 299→List Bool)
    (hR : A 31=UnaryTemplate.tape R) (hz : A 0=List.replicate R false)
    (hraw : A 32=List.replicate R true) (hlog : A 33=List.replicate (R+3) false)
    (hM : A 184=ZeroPadding.pad R (CompareMachine.word M))
    (hw : ∀j,A (widthSlots j)=List.replicate R false)
    (h185 : (A 185).length=R) (hcap : Completion.SourceDigitWidth.capacity (2*M)≤R) :
    Step phaseChange (phaseBudget R M) heads A heads
      (Function.update (Function.update A 184 (ZeroPadding.pad R (CompareMachine.word (2*M))))
        185 (ZeroPadding.pad R (CompareMachine.word (Completion.SourceDigitWidth.digitWidth (2*M))))) := by
  have hr : 2*M+1≤R := by unfold Completion.SourceDigitWidth.capacity at hcap;nlinarith
  have first:=double_run R M A hR hz hM (hw 1) hr
  have last:=regenerate_width_run R (2*M)
    (Function.update A 184 (ZeroPadding.pad R (CompareMachine.word (2*M))))
    (by simpa [Function.update] using hR) (by simpa [Function.update] using hraw)
    (by simpa [Function.update] using hlog) (by simp)
    (by intro j
        have hn:widthSlots j≠184 := by intro he;have hv:=congrArg Fin.val he;dsimp [widthSlots] at hv;omega
        simpa only [Function.update_of_ne hn] using hw j)
    (by simpa [Function.update] using h185) hcap
  have whole:=first.seq last
  have hf : (4*R+UnaryAddCount.budget M M+14)+1+
      (4*R+2*(2*M)+Completion.SourceDigitWidth.budget (2*M)+15)=phaseBudget R M := by unfold phaseBudget;omega
  rw [hf] at whole;exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
