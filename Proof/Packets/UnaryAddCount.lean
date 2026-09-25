import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.VectorCounter

/-! Add an actual unary count to a resident unary counter. The Repeat driver
is scanned and restored by the ordinary machine; no sum word is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.UnaryAddCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def machine := RepeatMachine.machine VectorCounter.increment (fun _ _=>true)
def budget (base count : Nat) := count*(2*(base+count)+5)+3

theorem run (R base count : Nat) :
    Step machine (budget base count) (fun _=>1)
      ![ZeroPadding.pad R (CompareMachine.word base),ZeroPadding.pad R (CompareMachine.word count)]
      (fun _=>1)
      ![ZeroPadding.pad R (CompareMachine.word (base+count)),ZeroPadding.pad R (CompareMachine.word count)] := by
  have h:=PhysicalRepeatStep.run VectorCounter.increment count (2*(base+count)+2)
    (fun _ _=>1) (fun k _=>ZeroPadding.pad R (CompareMachine.word (base+k)))
    (by intro k hk;exact (VectorCounter.increment_padded (base+k) R).enlarge (by omega))
  have padded:=h.pad (![0,R] : Fin 2→Nat)
  have hf : count*((2*(base+count)+2)+3)+3=budget base count := by unfold budget;ring
  rw [hf] at padded
  exact (padded.congr_in (by funext i;fin_cases i <;>rfl)
    (by funext i;fin_cases i <;>simp [Fin.addCases])).congr (by funext i;fin_cases i <;>rfl)
    (by funext i;fin_cases i <;>simp [Fin.addCases])

end
end PCJ9eff70d512234a4c_Fixed.Materializer.UnaryAddCount
