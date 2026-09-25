import Proof.Packets.PacketsXWalkLiteralMastersFanout

/-! Palette construction retains all seven actual source words. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace Theorem25Completion.WalkLiteralMasters

theorem source_retained (C R root rank depth M : Nat) (mask : List Bool) :
    ∀i : Fin 7,bank10 C R root rank depth M mask (i.castAdd 48)=
      input C R root rank depth M mask (i.castAdd 48) := by
  intro i;fin_cases i
  · change bank10 C R root rank depth M mask 0=_
    rw [bank10_other C R root rank depth M mask 0 (by decide)]
    rw [bank9_other C R root rank depth M mask 0 (by decide)]
    rw [bank8_other C R root rank depth M mask 0 (by decide)]
    rw [bank7_other C R root rank depth M mask 0 (by decide)]
    rw [bank6_other C R root rank depth M mask 0 (by decide)]
    rw [bank5_other C R root rank depth M mask 0 (by decide)]
    rw [bank4_other C R root rank depth M mask 0 (by decide)]
    exact bank3_slot C R root rank depth M mask 0
  · exact bank10_slot C R root rank depth M mask 23
  · exact bank10_slot C R root rank depth M mask 2
  · exact bank10_slot C R root rank depth M mask 3
  · change bank10 C R root rank depth M mask 4=_
    rw [bank10_other C R root rank depth M mask 4 (by decide)]
    rw [bank9_other C R root rank depth M mask 4 (by decide)]
    rw [bank8_other C R root rank depth M mask 4 (by decide)]
    exact bank7_slot C R root rank depth M mask 0
  · change bank10 C R root rank depth M mask 5=_
    rw [bank10_other C R root rank depth M mask 5 (by decide)]
    exact bank9_slot C R root rank depth M mask 0
  · exact bank10_slot C R root rank depth M mask 5

end Theorem25Completion.WalkLiteralMasters
