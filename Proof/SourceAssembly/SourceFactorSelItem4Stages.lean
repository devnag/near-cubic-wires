import Proof.SourceAssembly.SourceFactorSelInputMask

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Item4
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-! ## LM: lead ; mask ; frame, on `Fin (9 + (5 + w))` -/

section lm
variable (w : Nat)

/-- `0` retDrv · `1` drv · `2..5` ret · `6` lead log · `7` target · `8` framer log · `9 + j` mask worker tape `j`. -/
def lmRet (i : Fin 4) : Fin (9 + (5 + w)) := ⟨2 + i.val, by omega⟩
def lmMask (j : Fin (5 + w)) : Fin (9 + (5 + w)) := ⟨9 + j.val, by omega⟩

theorem lmMask_inj : Function.Injective (lmMask w) := by
  intro x y h
  have hv := congrArg Fin.val h
  simp only [lmMask] at hv
  exact Fin.ext (by omega)

def lmM (mask : MaskProducer) :=
  Composition.machine
    (SLoad.LeadDriver.machine (⟨0, by omega⟩ : Fin (9 + (5 + mask.work))) ⟨1, by omega⟩ (lmRet mask.work)
      (lmMask mask.work) ⟨6, by omega⟩)
    (Composition.machine (RecoveryFocus.machine (lmMask mask.work) mask.machine)
      (SLoad.MaskFrame.machine (lmMask mask.work ⟨4, by omega⟩) (⟨1, by omega⟩ : Fin (9 + (5 + mask.work)))
        ⟨7, by omega⟩ ⟨8, by omega⟩))

def lmCost (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) : Nat :=
  SLoad.LeadDriver.prefixFuel a r + 1 +
    (maskBudget mask.coefficient mask.degree (maskData a r) + 1 + (4 * r.q + 4))

/-- The exact entry (backing `R`). -/
def lmEntry (a : DecompositionAlgorithm) (r : Request) (R : Nat) (uK um : List Bool) (x : Fin (9 + (5 + w))) : List Bool :=
  if x.val = 0 then ZeroPadding.pad R (frame (List.replicate r.q true))
  else if x.val = 1 then []
  else if x.val = 2 then ZeroPadding.pad R (frame (r.supportWord a))
  else if x.val = 3 then ZeroPadding.pad R (frame (List.replicate r.q true))
  else if x.val = 4 then ZeroPadding.pad R (frame uK)
  else if x.val = 5 then ZeroPadding.pad R (frame um)
  else if 9 ≤ x.val ∧ x.val < 13 then []
  else List.replicate R false

theorem lm_run (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) (R : Nat) (uK um : List Bool)
    (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (cs : (r.supportWord a).length ≤ R) (cq : 4 * r.q + 3 ≤ R)
    (ck : 4 * uK.length + 3 ≤ R) (cm : 4 * um.length + 3 ≤ R) (cq2 : 2 * r.q + 1 ≤ R) :
    ∃ E' : Fin (9 + (5 + mask.work)) → List Bool,
      Step (lmM mask) (lmCost mask a r) (fun _ => 0) (lmEntry mask.work a r R uK um) (fun _ => 0) E' ∧
      E' ⟨7, by omega⟩ = ZeroPadding.pad R (frame (maskData a r).word) ∧
      (∀ x : Fin (9 + (5 + mask.work)), x.val ≠ 1 → x.val ≠ 7 → x.val < 9 → E' x = lmEntry mask.work a r R uK um x) := by
  classical
  have hinj := lmMask_inj mask.work
  have mv : ∀ j, (lmMask mask.work j).val = 9 + j.val := fun j => rfl
  have rv : ∀ i, (lmRet mask.work i).val = 2 + i.val := fun i => rfl
  have e1 := SLoad.LeadDriver.lead_driver_step mask (lmMask mask.work) hinj (lmRet mask.work)
    (⟨0, by omega⟩ : Fin (9 + (5 + mask.work))) ⟨1, by omega⟩ ⟨6, by omega⟩
    (by intro i j h; have := congrArg Fin.val h; rw [rv, mv] at this; omega)
    (by intro i h; have := congrArg Fin.val h; rw [rv] at this; simp at this; omega)
    (by intro j h; have := congrArg Fin.val h; rw [mv] at this; simp at this; omega)
    (by intro j h; have := congrArg Fin.val h; rw [mv] at this; simp at this; omega)
    (by intro i h; have := congrArg Fin.val h; rw [rv] at this; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by intro h; have := congrArg Fin.val h; simp at this)
    a r R (List.replicate r.q true) uK um List.length_replicate hk hmm cs (by rw [List.length_replicate]; exact cq)
    ck cm (fun _ => R) (fun _ => 0) (lmEntry mask.work a r R uK um)
    (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by
      intro j hj
      unfold lmEntry
      rw [mv]
      simp only [show 9 + j.val ≠ 0 by omega, show 9 + j.val ≠ 1 by omega, show 9 + j.val ≠ 2 by omega,
        show 9 + j.val ≠ 3 by omega, show 9 + j.val ≠ 4 by omega, show 9 + j.val ≠ 5 by omega, if_false]
      rw [if_pos ⟨by omega, by omega⟩])
    (by
      intro j hj
      unfold lmEntry
      rw [mv]
      simp only [show 9 + j.val ≠ 0 by omega, show 9 + j.val ≠ 1 by omega, show 9 + j.val ≠ 2 by omega,
        show 9 + j.val ≠ 3 by omega, show 9 + j.val ≠ 4 by omega, show 9 + j.val ≠ 5 by omega, if_false]
      rw [if_neg (by omega)])
    rfl
  have hz : ∀ {t : Nat} (sl : Fin t → Fin (9 + (5 + mask.work))), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => SLoad.dockH_existing sl _ _ (fun _ => rfl)
  rw [hz] at e1
  set A1 := Function.update (lmEntry mask.work a r R uK um) (⟨1, by omega⟩ : Fin (9 + (5 + mask.work)))
    (List.replicate r.q true) with hA1
  obtain ⟨B, hrunB, hword⟩ := mask.correct (maskData a r)
  have e2 := (hrunB.pad (SLoad.MaskInput.reserve (fun _ => R))).focus (lmMask mask.work) hinj (fun _ => 0) A1
  rw [hz] at e2
  set A2 := install (lmMask mask.work) A1 (fun i => ZeroPadding.pad (SLoad.MaskInput.reserve (fun _ => R) i) (B i))
    with hA2
  have hql : (B ⟨4, by omega⟩).length = r.q := by rw [hword]; exact SLoad.LeadDriver.word_length a r
  have off : ∀ x : Fin (9 + (5 + mask.work)), x.val < 9 → A2 x = A1 x := by
    intro x hx
    rw [hA2, install_other _ _ _ _ (fun j e => by have := congrArg Fin.val e; rw [mv] at this; omega)]
  have e3 := SLoad.MaskFrame.mask_frame_step (lmMask mask.work ⟨4, by omega⟩) (⟨1, by omega⟩ : Fin (9 + (5 + mask.work)))
    ⟨7, by omega⟩ ⟨8, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp [lmMask] at this)
    (by intro h; have := congrArg Fin.val h; simp [lmMask] at this)
    (by intro h; have := congrArg Fin.val h; simp [lmMask] at this)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (SLoad.MaskInput.reserve (fun _ => R) ⟨4, by omega⟩) 0 R R (B ⟨4, by omega⟩) (by rw [hql]; exact cq2)
    (fun _ => 0) A2 rfl rfl rfl rfl
    (by rw [hA2, install_slot _ hinj])
    (by
      rw [off _ (by simp), hA1, Function.update_self, ZeroPadding.pad_zero, hql])
    (by
      rw [off _ (by simp), hA1, Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp at this)]
      unfold lmEntry; simp)
    (by
      rw [off _ (by simp), hA1, Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp at this)]
      unfold lmEntry; simp)
  rw [hql] at e3
  refine ⟨_, e1.seq (e2.seq e3), ?_, ?_⟩
  · rw [Function.update_self, hword]
  · intro x h1 h7 h9
    rw [Function.update_of_ne (fun e => h7 (by rw [e])), off x h9, hA1,
      Function.update_of_ne (fun e => h1 (by rw [e]))]

theorem lm_entry_padded (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) (R : Nat) (uK um : List Bool)
    (j : Fin (9 + (5 + mask.work))) :
    ZeroPadding.pad R (lmEntry mask.work a r R uK um j) =
      if j.val = 0 then ZeroPadding.pad R (frame (List.replicate r.q true))
      else if j.val = 2 then ZeroPadding.pad R (frame (r.supportWord a))
      else if j.val = 3 then ZeroPadding.pad R (frame (List.replicate r.q true))
      else if j.val = 4 then ZeroPadding.pad R (frame uK)
      else if j.val = 5 then ZeroPadding.pad R (frame um)
      else List.replicate R false := by
  have hnil : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by simp [ZeroPadding.pad]
  unfold lmEntry
  by_cases h0 : j.val = 0
  · simp only [h0, if_true]; exact SourceRequest.InputPass.pad_pad_same _ _
  by_cases h1 : j.val = 1
  · simp only [h1, if_true, show (1 : Nat) ≠ 0 by omega, show (1 : Nat) ≠ 2 by omega, show (1 : Nat) ≠ 3 by omega,
      show (1 : Nat) ≠ 4 by omega, show (1 : Nat) ≠ 5 by omega, if_false]; exact hnil
  by_cases h2 : j.val = 2
  · simp only [h2, if_true, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, if_false]
    exact SourceRequest.InputPass.pad_pad_same _ _
  by_cases h3 : j.val = 3
  · simp only [h3, if_true, show (3 : Nat) ≠ 0 by omega, show (3 : Nat) ≠ 1 by omega, show (3 : Nat) ≠ 2 by omega, if_false]
    exact SourceRequest.InputPass.pad_pad_same _ _
  by_cases h4 : j.val = 4
  · simp only [h4, if_true, show (4 : Nat) ≠ 0 by omega, show (4 : Nat) ≠ 1 by omega, show (4 : Nat) ≠ 2 by omega,
      show (4 : Nat) ≠ 3 by omega, if_false]
    exact SourceRequest.InputPass.pad_pad_same _ _
  by_cases h5 : j.val = 5
  · simp only [h5, if_true, show (5 : Nat) ≠ 0 by omega, show (5 : Nat) ≠ 1 by omega, show (5 : Nat) ≠ 2 by omega,
      show (5 : Nat) ≠ 3 by omega, show (5 : Nat) ≠ 4 by omega, if_false]
    exact SourceRequest.InputPass.pad_pad_same _ _
  simp only [h0, h1, h2, h3, h4, h5, if_false]
  split_ifs
  · exact hnil
  · exact SourceRequest.InputPass.pad_blank R R le_rfl

/-- **LM docked, backing `R`**: the framed mask word on `sl 7`; every host tape off local `1, 7, ≥ 8` of the dock unchanged. -/
theorem lm_dock {U : Nat} (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) (R : Nat) (uK um : List Bool)
    (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (cs : (r.supportWord a).length ≤ R) (cq : 4 * r.q + 3 ≤ R)
    (ck : 4 * uK.length + 3 ≤ R) (cm : 4 * um.length + 3 ≤ R) (cq2 : 2 * r.q + 1 ≤ R)
    (sl : Fin (9 + (5 + mask.work)) → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hA : ∀ j, A (sl j) =
      if j.val = 0 then ZeroPadding.pad R (frame (List.replicate r.q true))
      else if j.val = 2 then ZeroPadding.pad R (frame (r.supportWord a))
      else if j.val = 3 then ZeroPadding.pad R (frame (List.replicate r.q true))
      else if j.val = 4 then ZeroPadding.pad R (frame uK)
      else if j.val = 5 then ZeroPadding.pad R (frame um)
      else List.replicate R false) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl (lmM mask)) (lmCost mask a r) H A H A' ∧
      A' (sl ⟨7, by omega⟩) = ZeroPadding.pad R (frame (maskData a r).word) ∧
      (∀ x, (∀ j, sl j = x → j.val < 9 ∧ j.val ≠ 1 ∧ j.val ≠ 7 ∧ j.val ≠ 8) → A' x = A x) := by
  obtain ⟨E', st, o7, kp⟩ := lm_run mask a r R uK um hk hmm cs cq ck cm cq2
  have d := (st.pad (fun _ => R)).dock sl hsl H A (fun j => hH j) (fun j => by rw [hA j, lm_entry_padded])
  rw [SLoad.dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_⟩
  · rw [install_slot sl hsl, o7, SourceRequest.InputPass.pad_pad_same]
  · intro x hx
    by_cases hp : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hp
      obtain ⟨h9, h1, h7, _⟩ := hx j rfl
      rw [install_slot sl hsl, kp j h1 h7 h9, lm_entry_padded, ← hA j]
    · exact install_other sl A _ x (fun j e => hp ⟨j, e⟩)

/-! ## TK: the K template, copied (`MatrixTemplateCopy` under `Rewind`) -/

/-- The template copier with its heads rewound (`Fin 5`: `0` source template, `1, 2` unary scratch, `3` the copy, `4` rewind log). -/
def tkM := Rewind.machine MatrixTemplateCopy.machine

theorem tk_run (n : Nat) :
    ∃ E' : Fin 5 → List Bool,
      Step tkM (2 * (2 * n + 5) + 2) (fun _ => 0) (Fin.addCases (MatrixTemplateCopy.input n) (fun _ : Fin 1 => []))
        (fun _ => 0) E' ∧
      E' 0 = UnaryTemplate.tape n ∧ E' 3 = UnaryTemplate.tape n := by
  obtain ⟨r, hr, h0, _, _, h3, hs⟩ := MatrixTemplateCopy.copy_run n
  obtain ⟨r', hr', hkeep, hheads, hsteps, _⟩ := Rewind.reset_run MatrixTemplateCopy.machine (2 * n + 5)
    (MatrixTemplateCopy.input n) r hr
  rw [hs] at hr'
  refine ⟨r'.final.tapes, Step.of_run hr' (funext hheads) rfl, ?_, ?_⟩
  · exact (hkeep 0).trans h0
  · exact (hkeep 3).trans h3

/-- **TK docked, backing `R`**: from `pad R (tape n)` on `sl 0` (kept) and blank `sl 1..4`, the copy `pad R (tape n)` on `sl 3`. -/
theorem tk_dock {U : Nat} (n R : Nat) (sl : Fin 5 → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hA0 : A (sl 0) = ZeroPadding.pad R (UnaryTemplate.tape n))
    (hbl : ∀ j : Fin 5, j ≠ 0 → A (sl j) = List.replicate R false) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl tkM) (2 * (2 * n + 5) + 2) H A H A' ∧
      A' (sl 3) = ZeroPadding.pad R (UnaryTemplate.tape n) ∧
      (∀ x, (∀ j, sl j = x → j = 0) → A' x = A x) := by
  obtain ⟨E', st, o0, o3⟩ := tk_run n
  have hnil : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by simp [ZeroPadding.pad]
  have d := (st.pad (fun _ => R)).dock sl hsl H A (fun j => hH j) (by
    intro j
    by_cases h : j = 0
    · subst h; exact hA0
    · rw [hbl j h]
      fin_cases j
      · exact absurd rfl h
      all_goals exact hnil.symm)
  rw [SLoad.dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_⟩
  · rw [install_slot sl hsl, o3]
  · intro x hx
    by_cases hp : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hp
      have := hx j rfl
      subst this
      rw [install_slot sl hsl, o0, hA0]
    · exact install_other sl A _ x (fun j e => hp ⟨j, e⟩)

/-- **MS docked, backing `R`**: from `pad R (exactListWord gs)` on `sl 0` and `pad R (tape q)` on `sl 12` (both kept), everything
else blank, the length `pad R 1^|exactListWord gs|` on `sl 15`. -/
theorem ms_dock {U q : Nat} (gs : List (ExactThresholdGate q)) (R : Nat) (sl : Fin 17 → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hA0 : A (sl 0) = ZeroPadding.pad R (exactListWord gs))
    (hA12 : A (sl 12) = ZeroPadding.pad R (UnaryTemplate.tape q))
    (hbl : ∀ j : Fin 17, j ≠ 0 → j ≠ 12 → A (sl j) = List.replicate R false) :
    ∃ A' : Fin U → List Bool,
      Step (RecoveryFocus.machine sl P1Closure.BinaryCacheColdMeasure.machine)
        (P1Closure.BinaryCacheColdMeasure.budget gs) H A H A' ∧
      A' (sl 15) = ZeroPadding.pad R (List.replicate (exactListWord gs).length true) ∧
      (∀ x, (∀ j, sl j = x → j = 0 ∨ j = 12) → A' x = A x) := by
  obtain ⟨T, st, t0, _, t12, t15⟩ := P1Closure.BinaryCacheColdMeasure.run gs
  have hnil : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by simp [ZeroPadding.pad]
  have d := (st.pad (fun _ => R)).dock sl hsl H A (fun j => hH j) (by
    intro j
    by_cases h0 : j = 0
    · subst h0; exact hA0
    by_cases h12 : j = 12
    · subst h12; exact hA12
    rw [hbl j h0 h12]
    fin_cases j <;> first | exact absurd rfl h0 | exact absurd rfl h12 | exact hnil.symm)
  rw [SLoad.dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_⟩
  · rw [install_slot sl hsl, t15]
  · intro x hx
    by_cases hp : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hp
      rcases hx j rfl with h | h
      · subst h; rw [install_slot sl hsl, t0, hA0]
      · subst h; rw [install_slot sl hsl, t12, hA12]
    · exact install_other sl A _ x (fun j e => hp ⟨j, e⟩)

end lm

end
end NearCubicWires.SourceFactorSel.Item4

