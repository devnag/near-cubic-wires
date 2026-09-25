import Proof.Packets.SourceResidentOccCount
import Proof.SourceAssembly.SourceFactorSelItem4Bank
import Proof.SourceAssembly.SourceFactorSelItem4Stages
import Proof.SourceAssembly.SourceFactorSelRunBound

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.RunBound
open NearCubicWires LocalBitMultitape ExtDecompositionBatch

/-- Writing one cell never shortens a tape. -/
theorem write_length_ge (l : List Bool) (h : Nat) (v : Bool) : l.length ≤ (writeTapeBit l h v).length := by
  induction l generalizing h with
  | nil => exact Nat.zero_le _
  | cons x t ih =>
    cases h with
    | zero => simp [writeTapeBit]
    | succ h =>
      simp only [writeTapeBit, List.length_cons]
      have := ih h
      omega

/-- One transition never shortens a tape. -/
theorem step_ge {t s : Nat} (p : Machine t s) (c d : Configuration t s) (hs : step p c = some d) (i : Fin t) :
    (c.tapes i).length ≤ (d.tapes i).length := by
  unfold step at hs
  obtain ⟨action, _, he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  simp only [applyAction]
  cases action.write i with
  | none => exact le_refl _
  | some v => exact write_length_ge _ _ _

/-- A whole run never shortens a tape. -/
theorem runFrom_ge {t s : Nat} (p : Machine t s) (fuel : Nat) (c : Configuration t s)
    (r : ExecutionReceipt t s) (hr : runFrom p fuel c = some r) (i : Fin t) :
    (c.tapes i).length ≤ (r.final.tapes i).length := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact le_refl _
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact le_refl _
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases he : runFrom p fuel d with
        | none => simp [hs, he] at hr
        | some tail =>
          simp only [hs, he, Option.some.injEq] at hr
          subst r
          exact (step_ge p c d hs i).trans (ih d tail he)

/-- **The `Step` form: a run never shortens a tape.** -/
theorem step_len_ge {t s : Nat} {p : Machine t s} {n : Nat} {H : Fin t → Nat} {A : Fin t → List Bool}
    {H' : Fin t → Nat} {A' : Fin t → List Bool} (h : Step p n H A H' A') (i : Fin t) :
    (A i).length ≤ (A' i).length := by
  obtain ⟨r, hr, _, ht, _⟩ := h
  have b := runFrom_ge p n ⟨p.start, H, A⟩ r hr i
  rw [ht] at b
  exact b

end NearCubicWires.SourceFactorSel.RunBound

namespace NearCubicWires.SourceFactorSel.Item4
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-! ## The cold-cache input word -/

theorem cold_input_nil {q : Nat} (r : BinaryCacheColdJoin.Args q) (j : Fin 373)
    (h98 : j.val ≠ 98) (h224 : j.val ≠ 224) (h225 : j.val ≠ 225) (h226 : j.val ≠ 226) :
    BinaryCacheColdRun.input r j = [] := by
  unfold BinaryCacheColdRun.input
  by_cases hj : j.val < 372
  · have e : j = Fin.castAdd 1 (⟨j.val, hj⟩ : Fin 372) := Fin.ext rfl
    rw [e, Fin.addCases_left]
    unfold BinaryCacheColdJoin.data0
    have n98 : (⟨j.val, hj⟩ : Fin 372) ≠ 98 := fun e => h98 (by have := congrArg Fin.val e; simpa using this)
    have n224 : (⟨j.val, hj⟩ : Fin 372) ≠ 224 := fun e => h224 (by have := congrArg Fin.val e; simpa using this)
    have n225 : (⟨j.val, hj⟩ : Fin 372) ≠ 225 := fun e => h225 (by have := congrArg Fin.val e; simpa using this)
    have n226 : (⟨j.val, hj⟩ : Fin 372) ≠ 226 := fun e => h226 (by have := congrArg Fin.val e; simpa using this)
    rw [if_neg n98, if_neg n224, if_neg n225, if_neg n226]
  · have e : j = Fin.natAdd 372 (⟨0, by omega⟩ : Fin 1) := Fin.ext (by simp; have := j.isLt; omega)
    rw [e, Fin.addCases_right]

/-! ## The unframer, padded and docked -/

theorem pad_nil_blank (R : Nat) : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by
  simp [ZeroPadding.pad]

/-- **The bare copy**: from `pad R (frame w)` on `sl 0`, blank `sl 1`, `sl 2` (at `R`), heads `0` there, the bare `pad R w` on
`sl 1`; heads unchanged; every tape other than `sl 1` kept. -/
theorem bare_dock {U : Nat} (sl : Fin 3 → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0) (R : Nat) (w : List Bool)
    (hw : w.length ≤ R)
    (h0 : A (sl 0) = ZeroPadding.pad R (RepairOrdinary.frame w)) (h1 : A (sl 1) = List.replicate R false)
    (h2 : A (sl 2) = List.replicate R false) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl Streaming.machine) (4 * w.length + 2) H A H A' ∧
      A' (sl 1) = ZeroPadding.pad R w ∧ ∀ x, (∀ j, sl j = x → j ≠ 1) → A' x = A x := by
  have st := (SLoad.Words.bare_step R w hw).pad (fun _ => R)
  have hin : ∀ j, A (sl j) = ZeroPadding.pad R (SLoad.Words.entry R w j) := by
    intro j
    fin_cases j
    · show A (sl 0) = ZeroPadding.pad R (ZeroPadding.pad R (RepairOrdinary.frame w))
      rw [SourceRequest.InputPass.pad_pad_same, h0]
    · show A (sl 1) = ZeroPadding.pad R []
      rw [pad_nil_blank, h1]
    · show A (sl 2) = ZeroPadding.pad R (List.replicate R false)
      rw [SourceRequest.InputPass.pad_blank R R (le_refl _), h2]
  have d := st.dock sl hsl H A (fun j => hH j) hin
  rw [SLoad.dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_⟩
  · rw [install_slot sl hsl]
    rfl
  · intro x hx
    by_cases hp : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hp
      have hj := hx j rfl
      rw [install_slot sl hsl]
      fin_cases j
      · show ZeroPadding.pad R (ZeroPadding.pad R (RepairOrdinary.frame w)) = A (sl 0)
        rw [SourceRequest.InputPass.pad_pad_same, h0]
      · exact absurd rfl hj
      · show ZeroPadding.pad R (List.replicate R false) = A (sl 2)
        rw [SourceRequest.InputPass.pad_blank R R (le_refl _), h2]
    · exact install_other sl A _ x (fun j e => hp ⟨j, e⟩)

/-! ## The index and pool blocks, docked -/

section blocks
variable {a : DecompositionAlgorithm} {k : Nat}

/-- **The index block, docked**: the framed index word on `sl ixOut` (head `0`), the inputs returned with heads `0`, every host tape
off the dock kept (word and head). -/
theorem idx_dock {U : Nat} (SB : StartBank a k) (r : Request) (R : Nat) (hR : SB.need r ≤ R)
    (sl : Fin ((132 + Cold.tapes a) + (6 + k)) → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hin : ∀ j, A (sl (ixIn SB j)) = ZeroPadding.pad R (inWord a r j))
    (hbl : ∀ x, (∀ j, ixIn SB j ≠ x) → A (sl x) = List.replicate R false) :
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step (RecoveryFocus.machine sl (idxBlock SB)) (idxCost SB r) H A H' A' ∧
      H' (sl (ixOut a k)) = 0 ∧ A' (sl (ixOut a k)) = ZeroPadding.pad R (RepairOrdinary.frame (r.indexWord a)) ∧
      (∀ j, A' (sl (ixIn SB j)) = A (sl (ixIn SB j)) ∧ H' (sl (ixIn SB j)) = 0) ∧
      (∀ x, (∀ y, sl y ≠ x) → A' x = A x ∧ H' x = H x) := by
  obtain ⟨H1, E1, st, o1, o2, o3⟩ := idx_block_run SB r R hR (fun y => A (sl y)) hin hbl
  have d := st.dock sl hsl H A (fun j => hH j) (fun j => rfl)
  refine ⟨_, _, d, ?_, ?_, ?_, ?_⟩
  · rw [dockH_slot _ hsl]; exact o1
  · rw [install_slot _ hsl]; exact o2
  · intro j
    rw [install_slot _ hsl, dockH_slot _ hsl]
    exact o3 j
  · intro x hx
    exact ⟨install_other _ _ _ _ hx, dockH_other _ _ _ _ hx⟩

/-- **The pool block, docked**: the whole cold-cache input on `sl (plOut j)` (heads `0`), the inputs returned with heads `0`, every
host tape off the dock kept. -/
theorem pool_dock {U : Nat} (selector : CyclicChoice.Laws) (SB : StartBank a k) (r : Request) (R : Nat) (hR : SB.need r ≤ R)
    (sl : Fin ((132 + Cold.tapes a) + (373 + k)) → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hin : ∀ j, A (sl (plIn SB j)) = ZeroPadding.pad R (inWord a r j))
    (hK : A (sl (plX a k 225)) = ZeroPadding.pad R (UnaryTemplate.tape (maskData a r).K))
    (hM : A (sl (plX a k 226)) = ZeroPadding.pad R (maskData a r).word)
    (hbl : ∀ x, (∀ j, plIn SB j ≠ x) → x ≠ plX a k 225 → x ≠ plX a k 226 → A (sl x) = List.replicate R false) :
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step (RecoveryFocus.machine sl (poolBlock SB)) (poolCost SB r) H A H' A' ∧
      (∀ j, H' (sl (plOut a k j)) = 0 ∧ A' (sl (plOut a k j)) = ZeroPadding.pad R
        (BinaryCacheColdRun.input (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) j)) ∧
      (∀ j, A' (sl (plIn SB j)) = A (sl (plIn SB j)) ∧ H' (sl (plIn SB j)) = 0) ∧
      (∀ x, (∀ y, sl y ≠ x) → A' x = A x ∧ H' x = H x) := by
  obtain ⟨H1, E1, st, o1, o2⟩ := pool_block_run selector SB r R hR (fun y => A (sl y)) hin hK hM hbl
  have d := st.dock sl hsl H A (fun j => hH j) (fun j => rfl)
  refine ⟨_, _, d, ?_, ?_, ?_⟩
  · intro j
    rw [dockH_slot _ hsl, install_slot _ hsl]
    exact o1 j
  · intro j
    rw [install_slot _ hsl, dockH_slot _ hsl]
    exact o2 j
  · intro x hx
    exact ⟨install_other _ _ _ _ hx, dockH_other _ _ _ _ hx⟩

/-- The pool block's output ports `98`, `224` lie in its bank, distinct. -/
theorem plOut98_lt : (plOut a k 98).val < 132 + Cold.tapes a := by
  have := (PCJ6e421fabe2aa4155_SourceCache.cachePort a).isLt
  simp [plOut, plI, PCJ6e421fabe2aa4155_SourceCache.poolSlots]

theorem plOut224_lt : (plOut a k 224).val < 132 + Cold.tapes a := by
  have := (PCJ6e421fabe2aa4155_SourceCache.domainPort a).isLt
  simp [plOut, plI, PCJ6e421fabe2aa4155_SourceCache.poolSlots]

theorem plOut98_ne224 : (plOut a k 98).val ≠ (plOut a k 224).val := by
  intro h
  have := PCJ6e421fabe2aa4155_SourceCache.poolSlots_injective a
    (Fin.ext (by simpa [plOut, plI] using h) : PCJ6e421fabe2aa4155_SourceCache.poolSlots a 98 =
      PCJ6e421fabe2aa4155_SourceCache.poolSlots a 224)
  exact absurd this (by decide)

end blocks

end
end NearCubicWires.SourceFactorSel.Item4

