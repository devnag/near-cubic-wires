

import Proof.Packets.PacketsXWalkTranscriptRewindRun

/-! Explicit paid return cost; every visited vertex contributes one row. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptRewind
open PCJ9eff70d512234a4c_Fixed.Materializer

theorem budget_eq (R N n : Nat) :
    budget R N n=(n+1)*(N*(4*R+10)+10)+1 := by
  unfold budget PacketVectorRewind.budget
  ring

theorem budget_le (R N n : Nat) (hN : 1≤N) :
    budget R N n≤(n+1)*N*(4*R+20)+1 := by
  rw [budget_eq]
  have per_row : N*(4*R+10)+10≤N*(4*R+20) := by nlinarith
  have all_rows:=Nat.mul_le_mul_left (n+1) per_row
  calc
    (n+1)*(N*(4*R+10)+10)+1≤(n+1)*(N*(4*R+20))+1 := Nat.add_le_add_right all_rows 1
    _=(n+1)*N*(4*R+20)+1 := by ring

end Theorem25Completion.WalkTranscriptRewind
