import Proof.PCP.ProjectionNormalizationForwardRules

namespace NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityProbe
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (left right : List Bool) (lp rp : ℕ) (eq found : Bool) : Configuration 4 s :=
  ⟨q,![lp,rp,0,0],![left,right,[eq],[found]]⟩
def boot : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,![none,none,some true,none],fun _ => .stay⟩ else none
def finish : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then some ⟨1,![none,none,none,some (xor (bits 3) (bits 2))],fun _ => .stay⟩ else none
def slots : Fin 3 → Fin 4 := ![0,1,2]
noncomputable def compareProgram := RecoveryFocus.machine slots ClauseEquality.machine
noncomputable def tailProgram := Composition.machine compareProgram finish
noncomputable def raw := Composition.machine boot tailProgram
noncomputable def rawFinal := (1 : Fin 2).natAdd (ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size)) |>.natAdd 2
noncomputable def machine := CursorRestore.machine raw 0
def budget (left right : Fin 3 → List Bool) := ClauseEquality.budget left right+4

theorem boot_run (left right : List Bool) (lp rp : ℕ) (eq found : Bool) :
    ∃ r,runFrom boot 1 (cfg 0 left right lp rp eq found)=some r ∧
      r.final=cfg 1 left right lp rp true found ∧ r.steps=1 := by
  have h : step boot (cfg 0 left right lp rp eq found)=some (cfg 1 left right lp rp true found) := by
    simp [step,boot,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem finish_run (left right : List Bool) (lp rp : ℕ) (eq found : Bool) :
    ∃ r,runFrom finish 1 (cfg 0 left right lp rp eq found)=some r ∧
      r.final=cfg 1 left right lp rp eq (xor found eq) ∧ r.steps=1 := by
  have he : readTapeBit [eq] 0=eq := rfl
  have hf : readTapeBit [found] 0=found := rfl
  have h : step finish (cfg 0 left right lp rp eq found)=some (cfg 1 left right lp rp eq (xor found eq)) := by
    simp [step,finish,cfg,Configuration.scanned,he,hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem compare_place (oldq q : Fin (ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size)))
    (left right : List Bool) (oldlp oldrp lp rp : ℕ) (oldeq eq found : Bool) :
    RecoveryFocus.config slots (cfg oldq left right oldlp oldrp oldeq found).heads
      (cfg oldq left right oldlp oldrp oldeq found).tapes (ClauseEquality.cfg q left right lp rp eq)=
      cfg q left right lp rp eq found := by
  apply TransitionEvent.focused_eq slots (by decide) (cfg oldq left right oldlp oldrp oldeq found)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 2 rfl)

theorem raw_forward (i : Fin 3) : CursorRestore.NoLeft raw (slots i) := by
  have hb : CursorRestore.NoLeft boot (slots i) := by
    intro q bits a ha
    simp only [boot] at ha
    split at ha
    · cases ha; simp
    · contradiction
  have hf : CursorRestore.NoLeft finish (slots i) := by
    intro q bits a ha
    simp only [finish] at ha
    split at ha
    · cases ha; simp
    · contradiction
  exact CursorRestore.composition_forward boot tailProgram (slots i) hb
    (CursorRestore.composition_forward compareProgram finish (slots i)
      (CursorRestore.focus_forward slots (by decide) ClauseEquality.machine i (CursorRestore.clause_forward i)) hf)

end NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityProbe
