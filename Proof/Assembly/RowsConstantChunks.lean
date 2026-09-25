import Proof.Assembly.RowsConstantSteps

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_Constants
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution

private theorem width_bounds (phase : Fin 13) : 0 < width phase.val ∧ width phase.val≤56 := by
  fin_cases phase <;> decide
private theorem blocks_width (phase : Fin 13) (i : Fin 11) :
    (blocks phase.val i).length≤width phase.val := by
  revert phase i
  decide

theorem emit_next (phase : Fin 13) (k : Fin 57) (he : Emits phase)
    (source : Fin 4 → List Bool) (H : Fin 4 → Nat) (out : Fin 11 → List Bool)
    (hk : k.val+1 < width phase.val) :
    step raw (cfg (code phase k) source H (partialOut out phase.val k.val))=
      some (cfg (incCode phase k) source H (partialOut out phase.val (k.val+1))) := by
  change (raw.rule (code phase k) _).map _=_
  rw [raw_emit_rule phase k he,if_pos hk]
  simp only [Option.map_some,emit_action,appended_partial]
  rfl

theorem emit_last (phase : Fin 13) (k : Fin 57) (he : Emits phase)
    (source : Fin 4 → List Bool) (H : Fin 4 → Nat) (out : Fin 11 → List Bool)
    (hk : k.val+1=width phase.val) :
    step raw (cfg (code phase k) source H (partialOut out phase.val k.val))=
      some (cfg (after phase.val) source (moved H phase.val true)
        (partialOut out phase.val (k.val+1))) := by
  change (raw.rule (code phase k) _).map _=_
  rw [raw_emit_rule phase k he,if_neg (by omega)]
  simp only [Option.map_some,emit_action,appended_partial]

theorem chunk_suffix (phase : Fin 13) (he : Emits phase)
    (source : Fin 4 → List Bool) (H : Fin 4 → Nat) (out : Fin 11 → List Bool)
    (remaining : Nat) (k : Fin 57) (hr : 0<remaining) (hk : k.val+remaining=width phase.val) :
    Timed raw remaining (cfg (code phase k) source H (partialOut out phase.val k.val))
      (cfg (after phase.val) source (moved H phase.val true)
        (partialOut out phase.val (width phase.val))) := by
  induction remaining generalizing k with
  | zero => omega
  | succ remaining ih =>
    cases remaining with
    | zero =>
      have hs:=emit_last phase k he source H out (by omega)
      rw [show k.val+1=width phase.val by omega] at hs
      exact Timed.single (raw_halted phase k) hs
    | succ remaining =>
      have hw:=(width_bounds phase).2
      let next : Fin 57 := ⟨k.val+1,by omega⟩
      have hs:=emit_next phase k he source H out (by omega)
      have hc : incCode phase k=code phase next := by apply Fin.ext;rfl
      rw [hc] at hs
      have path:=(Timed.single (raw_halted phase k) hs).trans
        (ih next (by omega) (by dsimp [next];omega))
      simpa only [Nat.add_comm 1] using path

theorem chunk (phase : Fin 13) (he : Emits phase)
    (source : Fin 4 → List Bool) (H : Fin 4 → Nat) (out : Fin 11 → List Bool) :
    Timed raw (width phase.val) (cfg (code phase 0) source H out)
      (cfg (after phase.val) source (moved H phase.val true)
        (fun i=>out i++blocks phase.val i)) := by
  have path:=chunk_suffix phase he source H out (width phase.val) 0
    (width_bounds phase).1 (by omega)
  have hi : partialOut out phase.val (0 : Fin 57).val=out := by funext i;simp [partialOut]
  have hf : partialOut out phase.val (width phase.val)=(fun i=>out i++blocks phase.val i) := by
    funext i
    simp only [partialOut,List.take_of_length_le (blocks_width phase i)]
  rw [hi,hf] at path
  exact path


end PCJ45bee56da9f34d5a_Constants
