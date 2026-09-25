import Proof.Assembly.Assembly
import Proof.SourceAssembly.SourceCleanupClass

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open RepairRepresentation SourceInterfaces
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
namespace NearCubicWires.SourceConstruction.Finish
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-! ## 1. The initializer's two tape groups -/

/-- Driver `k` of the initializer (the family bank is `Assembly.familyLocal`). -/
def driverLocal (a : WilliamsAlgorithm) (k : Fin 7) : Fin (initTapes a) := by
  unfold initTapes; exact k.natAdd (r_tapes a)

/-- The dock: family bank along `fam`, drivers along `drv`. -/
def joinSlots (a : WilliamsAlgorithm) {V : ℕ} (fam : Fin (r_tapes a) → Fin V) (drv : Fin 7 → Fin V) :
    Fin (initTapes a) → Fin V := by
  unfold initTapes; exact Fin.addCases fam drv

/-- The padding: `Rc` on the family bank (the clear's length), `cd k` on driver `k`. -/
def joinCaps (a : WilliamsAlgorithm) (Rc : ℕ) (cd : Fin 7 → ℕ) : Fin (initTapes a) → ℕ := by
  unfold initTapes; exact Fin.addCases (fun _ => Rc) cd

abbrev fl (a : WilliamsAlgorithm) (i : Fin (r_tapes a)) : Fin (initTapes a) :=
  PCJ2bf639ce0c7c470f_Assembly.familyLocal a i

theorem join_family (a : WilliamsAlgorithm) {V : ℕ} (fam : Fin (r_tapes a) → Fin V) (drv : Fin 7 → Fin V)
    (i : Fin (r_tapes a)) : joinSlots a fam drv (fl a i) = fam i := by
  change Fin.addCases (motive := fun _ => Fin V) fam drv (i.castAdd 7) = _
  rw [Fin.addCases_left]

theorem join_driver (a : WilliamsAlgorithm) {V : ℕ} (fam : Fin (r_tapes a) → Fin V) (drv : Fin 7 → Fin V)
    (k : Fin 7) : joinSlots a fam drv (driverLocal a k) = drv k := by
  change Fin.addCases (motive := fun _ => Fin V) fam drv (k.natAdd (r_tapes a)) = _
  rw [Fin.addCases_right]

theorem caps_family (a : WilliamsAlgorithm) (Rc : ℕ) (cd : Fin 7 → ℕ) (i : Fin (r_tapes a)) :
    joinCaps a Rc cd (fl a i) = Rc := by
  change Fin.addCases (motive := fun _ => ℕ) (fun _ => Rc) cd (i.castAdd 7) = _
  rw [Fin.addCases_left]

theorem caps_driver (a : WilliamsAlgorithm) (Rc : ℕ) (cd : Fin 7 → ℕ) (k : Fin 7) :
    joinCaps a Rc cd (driverLocal a k) = cd k := by
  change Fin.addCases (motive := fun _ => ℕ) (fun _ => Rc) cd (k.natAdd (r_tapes a)) = _
  rw [Fin.addCases_right]

/-- Every initializer tape is a family tape or a driver. -/
theorem init_cases (a : WilliamsAlgorithm) (P : Fin (initTapes a) → Prop)
    (hf : ∀ i, P (fl a i)) (hd : ∀ k, P (driverLocal a k)) : ∀ j, P j := by
  have key : ∀ x : Fin (r_tapes a + 7), P (cast (by unfold initTapes; rfl) x) := by
    intro x
    refine Fin.addCases (fun i => ?_) (fun k => ?_) x
    · exact hf i
    · exact hd k
  intro j
  have := key (cast (by unfold initTapes; rfl) j)
  simpa using this

theorem entry_family (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) (i : Fin (r_tapes a)) :
    entry a m D (fl a i) = if i = sourcePort a then D else [] := by
  change Fin.addCases (motive := fun _ => List Bool)
    (fun i : Fin (r_tapes a) => if i = sourcePort a then D else []) (drivers m) (i.castAdd 7) = _
  rw [Fin.addCases_left]

theorem entry_driver (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) (k : Fin 7) :
    entry a m D (driverLocal a k) = drivers m k := by
  change Fin.addCases (motive := fun _ => List Bool)
    (fun i : Fin (r_tapes a) => if i = sourcePort a then D else []) (drivers m) (k.natAdd (r_tapes a)) = _
  rw [Fin.addCases_right]

theorem entryH_family (a : WilliamsAlgorithm) (i : Fin (r_tapes a)) : entryH a (fl a i) = 0 := by
  change Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin (r_tapes a) => 0) (fun _ : Fin 7 => 1) (i.castAdd 7) = _
  rw [Fin.addCases_left]

theorem entryH_driver (a : WilliamsAlgorithm) (k : Fin 7) : entryH a (driverLocal a k) = 1 := by
  change Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin (r_tapes a) => 0) (fun _ : Fin 7 => 1)
    (k.natAdd (r_tapes a)) = _
  rw [Fin.addCases_right]

theorem exitT_family (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) (i : Fin (r_tapes a)) :
    exitT a m D (fl a i) = familyBank a m D i := by
  change Fin.addCases (motive := fun _ => List Bool) (familyBank a m D) (drivers m) (i.castAdd 7) = _
  rw [Fin.addCases_left]

/-- The dock is injective when its two halves are and never collide. -/
theorem joinSlots_injective (a : WilliamsAlgorithm) {V : ℕ} (fam : Fin (r_tapes a) → Fin V)
    (drv : Fin 7 → Fin V) (hf : Function.Injective fam) (hd : Function.Injective drv)
    (hfd : ∀ i k, fam i ≠ drv k) : Function.Injective (joinSlots a fam drv) := by
  intro x
  refine init_cases a (fun x => ∀ y, joinSlots a fam drv x = joinSlots a fam drv y → x = y) ?_ ?_ x
  · intro i y
    refine init_cases a (fun y => joinSlots a fam drv (fl a i) = joinSlots a fam drv y → fl a i = y) ?_ ?_ y
    · intro i' h
      rw [join_family, join_family] at h
      rw [hf h]
    · intro k h
      rw [join_family, join_driver] at h
      exact absurd h (hfd i k)
  · intro k y
    refine init_cases a (fun y => joinSlots a fam drv (driverLocal a k) = joinSlots a fam drv y →
      driverLocal a k = y) ?_ ?_ y
    · intro i h
      rw [join_driver, join_family] at h
      exact absurd h.symm (hfd i k)
    · intro k' h
      rw [join_driver, join_driver] at h
      rw [hd h]

/-! ## 2. The docked, padded initializer -/

theorem finish_core (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum)
    (S Rw B b v N Rc : ℕ) (cd : Fin 7 → ℕ) {V : ℕ}
    (fam : Fin (r_tapes a) → Fin V) (drv : Fin 7 → Fin V)
    (hinj : Function.Injective (joinSlots a fam drv))
    (H : Fin V → ℕ) (A : Fin V → List Bool)
    (hHf : ∀ i, H (fam i) = 0) (hHd : ∀ k, H (drv k) = 1)
    (hsrc : A (fam (sourcePort a)) =
      ZeroPadding.pad Rc (ds.flatMap (P1TopDownPaidReusable.Datum.word a)))
    (hblank : ∀ i, i ≠ sourcePort a → A (fam i) = List.replicate Rc false)
    (hdrv : ∀ k, A (drv k) = ZeroPadding.pad (cd k) (drivers ⟨S, Rw, B, b, v, N⟩ k)) :
    Step (RecoveryFocus.machine (joinSlots a fam drv) (PCJ34388a2fbfa9464b_.machine a))
      (initFuel a ⟨S, Rw, B, b, v, N⟩) H A
      (dockH (joinSlots a fam drv) H (exitH a))
      (install (joinSlots a fam drv) A (fun j => ZeroPadding.pad (joinCaps a Rc cd j)
        (exitT a ⟨S, Rw, B, b, v, N⟩ (ds.flatMap (P1TopDownPaidReusable.Datum.word a)) j))) := by
  have hrun := (PCJ34388a2fbfa9464b_.run a ⟨S, Rw, B, b, v, N⟩
    (ds.flatMap (P1TopDownPaidReusable.Datum.word a))).pad (joinCaps a Rc cd)
  refine hrun.dock (joinSlots a fam drv) hinj H A ?_ ?_
  · refine init_cases a _ (fun i => ?_) (fun k => ?_)
    · rw [join_family, entryH_family]; exact hHf i
    · rw [join_driver, entryH_driver]; exact hHd k
  · refine init_cases a _ (fun i => ?_) (fun k => ?_)
    · rw [join_family, caps_family, entry_family]
      by_cases hi : i = sourcePort a
      · subst hi; rw [if_pos rfl]; exact hsrc
      · rw [if_neg hi, hblank i hi]
        simp [ZeroPadding.pad]
    · rw [join_driver, caps_driver, entry_driver]; exact hdrv k

/-- The exit heads on the family slots are the consumer's `r_inputH` (`_hH`). -/
theorem finish_family_heads (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum)
    (S Rw B N : ℕ) {V : ℕ} (fam : Fin (r_tapes a) → Fin V) (drv : Fin 7 → Fin V)
    (hinj : Function.Injective (joinSlots a fam drv)) (H : Fin V → ℕ) (i : Fin (r_tapes a)) :
    dockH (joinSlots a fam drv) H (exitH a) (fam i) = r_inputH a ds S Rw B N i := by
  rw [← join_family a fam drv i, dockH_slot _ hinj]
  exact PCJ2bf639ce0c7c470f_Assembly.exit_heads_family a ds S Rw B N i

/-- The exit tapes on the family slots are `pad Rc (r_inputT …)`, i.e. `padded (j+1)` at
`reserveSize = Rc` with `A (j+1) (slots i) = r_inputT …` (`_hA`). -/
theorem finish_family_tapes (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum)
    (S Rw B b v N Rc : ℕ) (cd : Fin 7 → ℕ) {V : ℕ} (fam : Fin (r_tapes a) → Fin V)
    (drv : Fin 7 → Fin V) (hinj : Function.Injective (joinSlots a fam drv)) (A : Fin V → List Bool)
    (i : Fin (r_tapes a)) :
    install (joinSlots a fam drv) A (fun j => ZeroPadding.pad (joinCaps a Rc cd j)
        (exitT a ⟨S, Rw, B, b, v, N⟩ (ds.flatMap (P1TopDownPaidReusable.Datum.word a)) j)) (fam i) =
      ZeroPadding.pad Rc (r_inputT a ds S Rw B b v N i) := by
  rw [← join_family a fam drv i, install_slot _ hinj, caps_family, exitT_family,
    PCJ2bf639ce0c7c470f_Assembly.family_bank_input]

/-- Every other tape and head is untouched. -/
theorem finish_frame (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum)
    (S Rw B b v N Rc : ℕ) (cd : Fin 7 → ℕ) {V : ℕ} (fam : Fin (r_tapes a) → Fin V)
    (drv : Fin 7 → Fin V) (H : Fin V → ℕ) (A : Fin V → List Bool) (x : Fin V)
    (hx : ∀ j, joinSlots a fam drv j ≠ x) :
    dockH (joinSlots a fam drv) H (exitH a) x = H x ∧
    install (joinSlots a fam drv) A (fun j => ZeroPadding.pad (joinCaps a Rc cd j)
        (exitT a ⟨S, Rw, B, b, v, N⟩ (ds.flatMap (P1TopDownPaidReusable.Datum.word a)) j)) x = A x :=
  ⟨dockH_other _ _ _ _ hx, install_other _ _ _ _ hx⟩

/-! ## 3. The `Prepared` side: the rewound source port is the initializer's padded `D` -/

/-- The blank family tape is the clear's exit and the padded initializer entry. -/
theorem blank_is_padded (Rc : ℕ) : ZeroPadding.pad Rc ([] : List Bool) = List.replicate Rc false := by
  simp [ZeroPadding.pad]

/-! ## 4. The budget class of the core -/

end
end NearCubicWires.SourceConstruction.Finish
end
