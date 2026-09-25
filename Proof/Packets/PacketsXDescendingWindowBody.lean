import Proof.Packets.DescendingWindowCounters
import Proof.Packets.PacketsXWindowBankFacts

/-! One physically guarded elementary block in the exact normalized-window
source order. The actual unary degree descends while its binary complement
ascends. The existing emitter retains its zero-population branch. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsModeWindowLayout CloseoutRowsModeWindowScalar

private def counterSlots : Fin 3→Fin 60 := ![48,53,51]
noncomputable def counters := RecoveryFocus.machine counterSlots DescendingWindowCounters.machine
noncomputable def body := Composition.machine summand counters

theorem counters_run (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) (ha : a+1≤C) (hb : b+1<2^u) (hC : 2*u≤C) :
    Step counters (2*a+4*u+10) (heads out)
      (data v u M a offset b scratch degree target C nonzero guard out) (heads out)
      (data v u M (a-1) offset (b+1) scratch degree target C nonzero guard out) := by
  apply PhysicalFocusBoundary.focus (DescendingWindowCounters.run u a b C ha hb hC)
    counterSlots (by decide) (heads out) (heads out)
    (data v u M a offset b scratch degree target C nonzero guard out)
    (data v u M (a-1) offset (b+1) scratch degree target C nonzero guard out)
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i
    · exact (CloseoutRowsModeWindowCounter.degree_tape v u M a offset b scratch degree target C nonzero guard out).symm
    · rfl
    · exact (WindowBankFacts.log_tape _ _ _ _ _ _ _ _ _ _ _ _ _).symm
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i
    · exact (CloseoutRowsModeWindowCounter.degree_tape v u M (a-1) offset (b+1) scratch degree target C nonzero guard out).symm
    · rfl
    · exact (WindowBankFacts.log_tape _ _ _ _ _ _ _ _ _ _ _ _ _).symm
  · intro i away
    refine ⟨rfl,?_⟩
    have hi : i≠48 := by intro he;subst i;exact away 0 rfl
    rw [CloseoutRowsModeWindowCounter.degree_other v u M a (a-1) offset b scratch degree target C nonzero guard out i hi]
    exact WindowBankFacts.inner_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ i (by
      intro he;subst i;exact away 1 rfl)

def bodyBudget (v u M a C : Nat) :=
  2*a+20*u+39+CloseoutRowsModeElementaryReusable.budget v a M C

theorem body_run (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool)
    (hfit : offset+b<2^u) (hd : degree<2^u) (ht : target<2^u) (hscalar : 2*u≤C)
    (hb : b+1<2^u) (hMv : M≤2^v) (hmeta : 2*v+a+3≤C)
    (hC : CloseoutRowsModeElementary.budget v a M+1≤C) :
    Step body (bodyBudget v u M a C) (heads out)
      (data v u M a offset b scratch degree target C nonzero guard out)
      (heads (out++CloseoutRowsModeWindowEmit.word v a M (coefficient offset b degree target)))
      (data v u M (a-1) offset (b+1) (CloseoutRowsModeShift.top u offset b)
        degree target C (decide (offset+b≠0)) (coefficient offset b degree target)
        (out++CloseoutRowsModeWindowEmit.word v a M (coefficient offset b degree target))) := by
  have first:=summand_run v u M a offset b scratch degree target C nonzero guard out
    hfit hd ht hscalar hMv hmeta hC
  have last:=counters_run v u M a offset b (CloseoutRowsModeShift.top u offset b) degree target C
    (decide (offset+b≠0)) (coefficient offset b degree target)
    (out++CloseoutRowsModeWindowEmit.word v a M (coefficient offset b degree target)) (by omega) hb hscalar
  have whole:=first.seq last
  convert whole using 1 <;> first | rfl | (unfold bodyBudget;omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindow
