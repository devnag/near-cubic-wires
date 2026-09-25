import Proof.Packets.PacketVectorAppend

/-! Paid return across one vector of fixed-width packets. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketVectorRewind
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open VectorTransfer PacketVectorAppend
noncomputable section

def machine := Composition.machine VectorTransfer.backTarget VectorTransfer.backTarget
def budget (R N : Nat) := N*(4*R+10)+7

theorem run (R N spos pos : Nat) (source target : List Bool) :
    Step machine (budget R N) (heads spos (pos+N*(2*R))) (tapes R N source target)
      (heads spos pos) (tapes R N source target) := by
  have first:=backTarget_run R N spos (pos+N*R) source target
  have second:=backTarget_run R N spos pos source target
  have he : pos+N*R+N*R=pos+N*(2*R) := by ring
  rw [he] at first
  have joined:=first.seq second
  have fuel : N*(2*R+5)+3+1+(N*(2*R+5)+3)=budget R N := by unfold budget;ring
  simpa only [machine,fuel] using joined

theorem padded_run (R S N spos pos : Nat) (source target : List Bool) (hRS : R≤S) :
    Step machine (budget R N) (heads spos (pos+N*(2*R))) (paddedTapes R N S source target)
      (heads spos pos) (paddedTapes R N S source target) := by
  have padded:=(run R N spos pos source target).pad (![S,0,0,S,S,S] : Fin 6 → Nat)
  have eqn : (fun i=>ZeroPadding.pad ((![S,0,0,S,S,S] : Fin 6 → Nat) i)
      (tapes R N source target i))=paddedTapes R N S source target := by
    funext i;fin_cases i <;>
      simp [paddedTapes,tapes,ZeroPadding.pad_zero,ZeroPadding.pad,
        ←List.replicate_add,Nat.add_sub_of_le hRS]
  exact (padded.congr_in rfl eqn).congr rfl eqn

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketVectorRewind
