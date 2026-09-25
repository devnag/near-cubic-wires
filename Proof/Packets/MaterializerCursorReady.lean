import Proof.Packets.PhysicalParityRestore

/-! A reusable paid cursor return. Only an erased movement log is padded;
all source output bytes are preserved, and the selected entry cursor returns. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.CursorReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization

private theorem steps_le {t s : ℕ} (p : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some r) : r.steps ≤ fuel := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact Nat.le_refl _
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact Nat.zero_le _
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst r
          exact Nat.add_le_add_right (ih d tail ht) 1

noncomputable def input {t s : Nat} (c : Configuration t s) (cap : Nat) :=
  ZeroPadding.config (Rewind.Workspace.capacities t cap) (Rewind.recording c 0)

def ending {t s : Nat} (target : Fin t) (entry result : Configuration t s) (cap : Nat) :=
  SelectiveReset.finished (s:=s) (fun i=>if i=target then entry.heads i else result.heads i) result.tapes cap

theorem run {t s : Nat} (p : Machine t s) (target : Fin t) (forward : CursorRestore.NoLeft p target)
    (fuel cap : Nat) (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c=some source) (hcap : fuel≤cap) :
    ∃ r,runFrom (CursorRestore.machine p target) (2*fuel+2) (input c cap)=some r ∧
      r.steps≤2*fuel+2 ∧ r.final=ending target c source.final cap := by
  have hs := steps_le p fuel c source hr
  obtain ⟨base,log,hb,hl,hbs,hbf⟩ := CursorRestore.restore_run p target forward fuel c source hr
  obtain ⟨r,hrr,hrf,hrs,_⟩ := ZeroPadding.run_config (CursorRestore.machine p target)
    (Rewind.Workspace.capacities t cap) _ _ base hb
  have hbnd : 2*source.steps+2≤2*fuel+2 := by omega
  have more := runFrom_moreFuel (CursorRestore.machine p target) _
    (2*fuel+2-(2*source.steps+2)) _ r hrr
  rw [Nat.add_sub_of_le hbnd] at more
  refine ⟨r,more,?_,?_⟩
  · rw [hrs,hbs]; omega
  · rw [hrf,hbf,SelectiveReset.padded_finished,max_eq_left (hl.trans (hs.trans hcap))]
    rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.CursorReady
