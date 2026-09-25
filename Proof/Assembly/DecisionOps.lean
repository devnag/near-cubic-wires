import Proof.Assembly.State

/-! Actual decision calls on their nonzero entry cursors. Native receipts
are transported once; the ambient bank changes only at the written port. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.DecisionOps
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
instance sizesNeZero (j : Fin 5) : NeZero (Program.sizes j) :=
  ⟨by fin_cases j <;> decide⟩

theorem focus_preserving {t u s : Nat} (p : Machine t s)
    (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (H : Fin u → Nat) (A : Fin u → List Bool) (c e : Configuration t s)
    (fuel : Nat) (native : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some native) (hf : native.final = e)
    (he : e.heads = c.heads)
    (hh : ∀ j, H (slot j) = c.heads j) (hb : ∀ j, A (slot j) = c.tapes j) :
    ∃ r, runFrom (RecoveryFocus.machine slot p) fuel ⟨c.control,H,A⟩ = some r ∧
      r.final = ⟨e.control,H,install slot A e.tapes⟩ ∧ r.steps = native.steps := by
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config slot hi p H A fuel c native hr
  have hc := WilliamsSourceCrop.focus_same slot (⟨c.control,H,A⟩ : Configuration u s) c hh hb
  rw [hc] at hrun
  refine ⟨r,hrun,?_,hsteps⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp only [RecoveryFocus.config,hp]
    | some j =>
      simp only [RecoveryFocus.config,hp]
      rw [he]
      exact (hh j).symm.trans (congrArg H (RecoveryFocus.slot_of_pick slot hp))
  · rfl

theorem install_one {t u : Nat} (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (A : Fin u → List Bool) (output : Fin t → List Bool) (j : Fin t) (value : List Bool)
    (hj : output j = value) (ho : ∀ k, k ≠ j → output k = A (slot k)) :
    install slot A output = Function.update A (slot j) value := by
  classical
  funext i
  by_cases he : i = slot j
  · subst i
    simp only [install_slot slot hi,Function.update_self,hj]
  · cases hp : RecoveryFocus.pick slot i with
    | none => simp only [install,hp,Function.update_of_ne he]
    | some k =>
      have hs := RecoveryFocus.slot_of_pick slot hp
      have hk : k ≠ j := by intro h; subst k; exact he hs.symm
      simp only [install,hp,Function.update_of_ne he]
      exact (ho k hk).trans (congrArg A hs)

def pairCapacity (best : Nat) : Fin 2 → Nat := ![best+1,0]

theorem compare (H : Fin 13 → Nat) (A : Fin 13 → List Bool) (n best : Nat)
    (h8 : H 8 = 1) (h11 : H 11 = 1)
    (a8 : A 8 = ZeroPadding.pad (best+1) (CompareMachine.word n))
    (a11 : A 11 = CompareMachine.word best) :
    ∃ r, runFrom (Program.parts 0) (2*min n best+3) ⟨0,H,A⟩ = some r ∧
      r.final = ⟨if n ≤ best then 5 else 6,H,A⟩ ∧ r.steps = 2*min n best+3 := by
  obtain ⟨s,hs,hf,ht,_⟩ := CompareMachine.compare_run n best
  obtain ⟨p,hp,hpf,hpt,_⟩ := ZeroPadding.run_config CompareMachine.machine (pairCapacity best) _ _ s hs
  have hh : ∀ j, H (Program.compareSlots j) =
      (ZeroPadding.config (pairCapacity best) (CompareMachine.cfg 0 n best 1)).heads j := by
    intro j; fin_cases j <;> assumption
  have hb : ∀ j, A (Program.compareSlots j) =
      (ZeroPadding.config (pairCapacity best) (CompareMachine.cfg 0 n best 1)).tapes j := by
    intro j; fin_cases j
    · exact a8
    · simpa [ZeroPadding.config,pairCapacity,CompareMachine.cfg,Program.compareSlots] using a11
  obtain ⟨r,hr,hrf,hrt⟩ := focus_preserving CompareMachine.machine Program.compareSlots
    Program.compareSlots_injective H A _ _ _ p hp (hpf.trans (congrArg _ hf)) rfl hh hb
  have hout : install Program.compareSlots A
      (ZeroPadding.config (pairCapacity best)
        (CompareMachine.cfg (if n ≤ best then 5 else 6) n best 1)).tapes = A :=
    install_existing _ _ _ hb
  refine ⟨r,hr,?_,hrt.trans (hpt.trans ht)⟩
  rw [hout] at hrf
  apply hrf.trans
  apply configuration_ext
  · apply Fin.ext
    simp only [ZeroPadding.config, CompareMachine.cfg]
    split_ifs <;> decide
  · rfl
  · rfl

theorem best (H : Fin 13 → Nat) (A : Fin 13 → List Bool) (n old : Nat)
    (h8 : H 8 = 1) (h11 : H 11 = 1)
    (a8 : A 8 = ZeroPadding.pad (old+1) (CompareMachine.word n))
    (a11 : A 11 = CompareMachine.word old) :
    ∃ r, runFrom (Program.parts 1) (2*n+2) ⟨0,H,A⟩ = some r ∧
      r.final = ⟨2,H,Function.update A 11 (CompareMachine.word (max old n))⟩ ∧
      r.steps = 2*n+2 := by
  obtain ⟨s,hs,hf,ht⟩ := Best.best_run n old
  obtain ⟨p,hp,hpf,hpt,_⟩ := ZeroPadding.run_config Best.machine (pairCapacity old) _ _ s hs
  have hh : ∀ j, H (Program.compareSlots j) =
      (ZeroPadding.config (pairCapacity old) (Best.scanCfg n old 0)).heads j := by
    intro j; fin_cases j <;> assumption
  have hb : ∀ j, A (Program.compareSlots j) =
      (ZeroPadding.config (pairCapacity old) (Best.scanCfg n old 0)).tapes j := by
    intro j; fin_cases j
    · exact a8
    · simpa [ZeroPadding.config,pairCapacity,Best.scanCfg,Program.compareSlots] using a11
  obtain ⟨r,hr,hrf,hrt⟩ := focus_preserving Best.machine Program.compareSlots
    Program.compareSlots_injective H A _ _ _ p hp (hpf.trans (congrArg _ hf)) rfl hh hb
  have hout : install Program.compareSlots A
      (ZeroPadding.config (pairCapacity old) (Best.finished n old)).tapes =
      Function.update A 11 (CompareMachine.word (max old n)) := by
    apply install_one Program.compareSlots Program.compareSlots_injective A _ 1
    · simp [ZeroPadding.config,pairCapacity,Best.finished]
    · intro k hk
      fin_cases k
      · exact a8.symm
      · exact False.elim (hk rfl)
  refine ⟨r,hr,?_,hrt.trans (hpt.trans ht)⟩
  rw [hout] at hrf
  apply hrf.trans
  apply configuration_ext
  · apply Fin.ext
    simp [Program.sizes, ZeroPadding.config, Best.finished]
  · rfl
  · rfl

theorem clear (H : Fin 13 → Nat) (A : Fin 13 → List Bool) (n old : Nat)
    (h8 : H 8 = 1) (a8 : A 8 = ZeroPadding.pad (old+1) (CompareMachine.word n)) :
    ∃ r, runFrom (Program.parts 3) (2*n+2) ⟨0,H,A⟩ = some r ∧
      r.final = ⟨2,H,Function.update A 8 (List.replicate (max old n+1) false)⟩ ∧
      r.steps = 2*n+2 := by
  obtain ⟨s,hs,hf,ht⟩ := Clear.clear_run n
  obtain ⟨p,hp,hpf,hpt,_⟩ := ZeroPadding.run_config Clear.machine (fun _ => old+1) _ _ s hs
  have hh : ∀ j, H (Program.clearSlots j) =
      (ZeroPadding.config (fun _ => old+1) (Clear.scanCfg n 0)).heads j := by
    intro j; fin_cases j; exact h8
  have hb : ∀ j, A (Program.clearSlots j) =
      (ZeroPadding.config (fun _ => old+1) (Clear.scanCfg n 0)).tapes j := by
    intro j; fin_cases j; exact a8
  obtain ⟨r,hr,hrf,hrt⟩ := focus_preserving Clear.machine Program.clearSlots
    Program.clearSlots_injective H A _ _ _ p hp (hpf.trans (congrArg _ hf)) rfl hh hb
  have hout : install Program.clearSlots A
      (ZeroPadding.config (fun _ => old+1) (Clear.finished n)).tapes =
      Function.update A 8 (List.replicate (max old n+1) false) := by
    apply install_one Program.clearSlots Program.clearSlots_injective A _ 0
    · exact State.candidate_cleared old n
    · intro k hk; fin_cases k; exact False.elim (hk rfl)
  refine ⟨r,hr,?_,hrt.trans (hpt.trans ht)⟩
  rw [hout] at hrf
  apply hrf.trans
  apply configuration_ext
  · apply Fin.ext
    simp [Program.sizes, ZeroPadding.config, Clear.finished]
  · rfl
  · rfl

theorem copy (H : Fin 13 → Nat) (A : Fin 13 → List Bool)
    (pre xs old tail : List Bool) (hlen : old.length = xs.length)
    (h1 : H 1 = 1) (h5 : H 5 = pre.length) (h4 : H 4 = 0)
    (a1 : A 1 = CompareMachine.word xs.length)
    (a5 : A 5 = pre++xs++tail) (a4 : A 4 = old) :
    ∃ r, runFrom (Program.parts 2) (2*xs.length+2) ⟨0,H,A⟩ = some r ∧
      r.final = ⟨2,H,Function.update A 4 xs⟩ ∧ r.steps = 2*xs.length+2 := by
  obtain ⟨s,hs,hf,ht⟩ := Copy.copy_run pre xs old tail hlen
  have hh : ∀ j, H (Program.copySlots j) =
      (Copy.scanCfg xs.length pre [] xs old tail).heads j := by
    intro j; fin_cases j
    · exact h1
    · simpa [Copy.scanCfg,Program.copySlots] using h5
    · exact h4
  have hb : ∀ j, A (Program.copySlots j) =
      (Copy.scanCfg xs.length pre [] xs old tail).tapes j := by
    intro j; fin_cases j
    · exact a1
    · simpa [Copy.scanCfg,Program.copySlots] using a5
    · exact a4
  have he : (Copy.finished xs.length pre xs tail).heads =
      (Copy.scanCfg xs.length pre [] xs old tail).heads := by
    funext j; fin_cases j <;> simp [Copy.finished,Copy.scanCfg]
  obtain ⟨r,hr,hrf,hrt⟩ := focus_preserving Copy.machine Program.copySlots
    Program.copySlots_injective H A _ _ _ s hs hf he hh hb
  have hout : install Program.copySlots A (Copy.finished xs.length pre xs tail).tapes =
      Function.update A 4 xs := by
    apply install_one Program.copySlots Program.copySlots_injective A _ 2
    · rfl
    · intro k hk; fin_cases k
      · exact a1.symm
      · exact a5.symm
      · exact False.elim (hk rfl)
  refine ⟨r,hr,?_,hrt.trans ht⟩
  rw [hout] at hrf
  apply hrf.trans
  apply configuration_ext
  · apply Fin.ext
    simp [Program.sizes, Copy.finished]
  · rfl
  · rfl

end PCJ93d4cfe17dc847a3.DecisionOps
