import Proof.Rows.MaskReverse

set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverse
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def machine := RepeatMachine.machine body (fun _ _ => true)
noncomputable def loopCfg (phase : Fin 5) (B pos : Nat) (source out : List Bool) (total driver : Nat) :=
  RepeatMachine.cfg phase (cfg body.start B 1 pos source out) total driver

theorem body_control (q : Fin 5) (phase : Fin 5) (B pos : Nat) (source out : List Bool) (total driver : Nat) :
    RepeatMachine.cfg phase (cfg q B 1 pos source out) total driver =
      loopCfg phase B pos source out total driver := rfl

theorem reverse_remaining (B : Nat) (rows : List (List Bool)) (pre suffix out : List Bool)
    (total pos : Nat) (hn : pos+rows.length=total) (hw : ∀ row ∈ rows, row.length=B) :
    Timed machine (rows.length*(4*B+6)+total+3)
      (loopCfg 0 B (pre.length+rows.flatten.length) (pre++rows.flatten++suffix) out total (pos+1))
      (loopCfg 3 B pre.length (pre++rows.flatten++suffix) (out++rows.reverse.flatten) total 1) := by
  induction rows using List.reverseRecOn generalizing pre suffix out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa [machine,loopCfg] using RepeatMachine.exhaust body (fun _ _ => true)
      (cfg body.start B 1 pre.length (pre++suffix) out) total
  | append_singleton rows row ih =>
    have hrow : row.length=B := hw row (by simp)
    have hrows : ∀ r ∈ rows, r.length=B := fun r hr => hw r (by simp [hr])
    obtain ⟨r,hr,hf,hs⟩ := row_run row (pre++rows.flatten) suffix out
    have first := RepeatMachine.iteration body (fun _ _ => true)
      (cfg 0 row.length 1 ((pre++rows.flatten).length+row.length)
        ((pre++rows.flatten)++row++suffix) out) total pos r rfl
      (by simp only [List.length_append,List.length_singleton] at hn; omega) hr
    rw [hf,hs,body_control,body_control,hrow] at first
    change Timed machine (4*B+4+2)
      (loopCfg 0 B ((pre++rows.flatten).length+B) ((pre++rows.flatten)++row++suffix) out total (pos+1))
      (loopCfg 0 B (pre++rows.flatten).length ((pre++rows.flatten)++row++suffix) (out++row) total (pos+2)) at first
    have rest := ih pre (row++suffix) (out++row) (pos+1)
      (by simp only [List.length_append,List.length_singleton] at hn; omega) hrows
    have h := first.trans (by simpa [List.length_append,List.append_assoc,Nat.add_assoc] using rest)
    have time : (4*B+4+2)+(rows.length*(4*B+6)+total+3)=
      (rows.length+1)*(4*B+6)+total+3 := by ring
    simp only [Nat.add_assoc] at time h
    rw [time] at h
    simpa [List.flatten_append,List.flatten_cons,List.reverse_append,List.append_assoc,
      List.length_append,hrow,Nat.add_assoc] using h

theorem reverse_run (B : Nat) (rows : List (List Bool)) (pre suffix out : List Bool)
    (hw : ∀ row ∈ rows, row.length=B) :
    ∃ r, runFrom machine (rows.length*(4*B+7)+3)
      (loopCfg 0 B (pre.length+rows.flatten.length) (pre++rows.flatten++suffix) out rows.length 1)=some r ∧
      r.final=loopCfg 3 B pre.length (pre++rows.flatten++suffix) (out++rows.reverse.flatten) rows.length 1 ∧
      r.steps=rows.length*(4*B+7)+3 := by
  have h := reverse_remaining B rows pre suffix out rows.length 0 (by omega) hw
  have time : rows.length*(4*B+6)+rows.length+3=rows.length*(4*B+7)+3 := by ring
  rw [time] at h
  simpa only [Nat.zero_add] using h.run (by
    simp [machine,loopCfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverse
