import Proof.Packets.GradedWindowFromRoot

/-! Each level pays to erase the previous window counter before generating
its replacement, so a retained W master can be reused across descending levels. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def clearOutput := PhysicalCopyInto.machine (12 : Fin 13) 1 9
def reusable := Composition.machine clearOutput machine

theorem clear_output (R root level old : Nat) (hr : old+1≤R) :
    Step clearOutput (2*R+2) (H 1 0) (A R root level 0 0 old)
      (H 1 0) (A R root level 0 0 0) := by
  have h:=PhysicalCopyInto.run R (12 : Fin 13) 1 9 (by decide) (by decide) (by decide)
    (H 1 0) (A R root level 0 0 old) rfl rfl rfl rfl
    (by simp [A]) (by simp [A,ZeroPadding.pad_length,CompareMachine.word];omega)
  exact h.congr rfl (by funext i;fin_cases i <;>simp [A,Function.update,zero_count R (by omega)])

theorem reusable_run (R root level old : Nat) (hroot : root+67≤R) (hlevel : level+2≤R)
    (hold : old+1≤R) :
    Step reusable (2*R+3+budget R root level) (H 1 0) (A R root level 0 0 old)
      (H 1 0) (A R root level 0 0 (window root level)) := by
  have h:=(clear_output R root level old hold).seq (run R root level hroot hlevel)
  have hf : (2*R+2)+1+budget R root level=2*R+3+budget R root level := by omega
  rw [hf] at h;exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
