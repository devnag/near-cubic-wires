import Proof.SourceAssembly.SourceFactorSelWordsRunA

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Words
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-- The cold input's K template is the mask's live count (the geometry's `card`). -/
theorem cold_input_225 (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (r : Request) :
    BinaryCacheColdRun.input (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) 225 =
      UnaryTemplate.tape (maskData a r).K := by
  show UnaryTemplate.tape (Packets.live (r.family a)).card = _
  rw [(geometryOf selector a r).card]
  rfl

theorem cold_input_226 (a : DecompositionAlgorithm) (r : Request) :
    BinaryCacheColdRun.input (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) 226 = (maskData a r).word := rfl

section stages
variable {w C k : Nat} (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc : Nat)

/-! ## Stage 6: the K template -/

theorem st6 (E : Fin (nW w C k) → List Bool) (H : Fin (nW w C k) → Nat) (hWI : WI a r MB Rc 5 (o6 w C k) E H) :
    ∃ E', Step (RecoveryFocus.machine (m6 w C k) Item4.tkM) (2 * (2 * (maskData a r).K + 5) + 2) H E H E' ∧
      WI a r MB Rc 6 (o7 w C k) E' H := by
  have hb : ∀ i, 30 ≤ o6 w C k + i := fun i => by unfold o6; omega
  have sc : ∀ j, (m6 w C k j).val < 30 ∨ o6 w C k ≤ (m6 w C k j).val := by
    intro j; rcases v6_cases w C k j.val with h | h
    · left; exact h
    · right; show o6 w C k ≤ v6 _ _ _ j.val; omega
  have hE : ∀ j, E (m6 w C k j) = Gn a r MB Rc 5 (v6 w C k j.val) := fun j => (hWI _ (sc j)).1
  obtain ⟨E', st, out, fr⟩ := Item4.tk_dock (maskData a r).K Rc (m6 w C k) (m6_inj w C k) H E (fun j => (hWI _ (sc j)).2)
    (by rw [hE]; rfl)
    (by
      intro j hj
      rw [hE]
      fin_cases j
      · exact absurd rfl hj
      all_goals first
        | rfl
        | exact gn_high (hb _))
  refine ⟨E', st, wi_next hWI (by unfold o6 o7; omega) ?_ ?_⟩
  · intro x hx hp
    refine ⟨?_, (hWI x (by omega)).2⟩
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    interval_cases xv <;> first
      | (exact absurd hp (by decide))
      | (exact out)
  · intro x hx hn
    refine ⟨fr x ?_, rfl⟩
    intro j hj
    have hv : v6 w C k j.val = x.val := congrArg Fin.val hj
    rcases v6_cases w C k j.val with h | h
    · fin_cases j
      · rfl
      all_goals exfalso
      all_goals first
        | (exact hn ⟨hv ▸ h, by rw [← hv]; rfl⟩)
        | (exact absurd h (Nat.not_lt.mpr (hb _)))
    · exfalso
      have := j.isLt
      unfold o6 o7 at *
      omega

/-! ## Stage 7: the pool block (P's start bank ; the accepted cache run) -/

theorem v7_98 (p98 p224 : Nat) : v7 w C k p98 p224 p98 = 25 := by unfold v7; rw [if_pos rfl]
theorem v7_224 (p98 p224 : Nat) (hne : p98 ≠ p224) : v7 w C k p98 p224 p224 = 26 := by
  unfold v7; rw [if_neg (Ne.symm hne), if_pos rfl]
theorem v7_x (p98 p224 : Nat) (h98 : p98 < 132 + C) (h224 : p224 < 132 + C) (j : Nat) (hj : j < 2) :
    v7 w C k p98 p224 (132 + C + 225 + j) = 27 + j := by
  unfold v7; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
theorem v7_in (p98 p224 : Nat) (h98 : p98 < 132 + C) (h224 : p224 < 132 + C) (j : Nat) (hj : j < 5) :
    v7 w C k p98 p224 (132 + C + 373 + j) = t7 j := by
  unfold v7; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega

/-- The pool block's two bank outputs, by value. -/
def q98 (a : DecompositionAlgorithm) (k : Nat) : Nat := (Item4.plOut a k 98).val
def q224 (a : DecompositionAlgorithm) (k : Nat) : Nat := (Item4.plOut a k 224).val
/-- The pool block's dock. -/
def M7 (w : Nat) (a : DecompositionAlgorithm) (k : Nat) := m7 w (Cold.tapes a) k (q98 a k) (q224 a k)

theorem q98_lt : q98 a k < 132 + Cold.tapes a := Item4.plOut98_lt
theorem q224_lt : q224 a k < 132 + Cold.tapes a := Item4.plOut224_lt
theorem q_ne : q98 a k ≠ q224 a k := Item4.plOut98_ne224

theorem M7_val (w : Nat) (y : Fin ((132 + Cold.tapes a) + (373 + k))) :
    (M7 w a k y).val = v7 w (Cold.tapes a) k (q98 a k) (q224 a k) y.val := rfl

theorem M7_inj (w : Nat) : Function.Injective (M7 w a k) :=
  m7_inj w (Cold.tapes a) k _ _ Item4.plOut98_lt Item4.plOut224_lt

theorem M7_sc (w : Nat) (y : Fin ((132 + Cold.tapes a) + (373 + k))) :
    (M7 w a k y).val < 30 ∨ o7 w (Cold.tapes a) k ≤ (M7 w a k y).val := by
  rcases v7_cases w (Cold.tapes a) k (q98 a k) (q224 a k) y.val with h | h
  · left; exact h
  · right; rw [M7_val, h]; omega

theorem plIn_v (SB : Item4.StartBank a k) (hIn : ∀ j, (SB.inPort j).val = j.val) (j : Fin 5) :
    (Item4.plIn SB j).val = 132 + Cold.tapes a + 373 + j.val := by
  rw [Item4.plIn_val, hIn]

theorem st7_in (w : Nat) (SB : Item4.StartBank a k) (hIn : ∀ j, (SB.inPort j).val = j.val)
    (E : Fin (nW w (Cold.tapes a) k) → List Bool) (H : Fin (nW w (Cold.tapes a) k) → Nat) (hWI : WI a r MB Rc 6 (o7 w (Cold.tapes a) k) E H)
    (j : Fin 5) : E (M7 w a k (Item4.plIn SB j)) = ZeroPadding.pad Rc (Item4.inWord a r j) := by
  rw [(hWI _ (M7_sc a w _)).1, M7_val, plIn_v a SB hIn,
    v7_in (w := w) (k := k) (q98 a k) (q224 a k) (q98_lt a) (q224_lt a) _ j.isLt]
  fin_cases j <;> rfl

theorem st7_x (w : Nat) (E : Fin (nW w (Cold.tapes a) k) → List Bool)
    (H : Fin (nW w (Cold.tapes a) k) → Nat) (hWI : WI a r MB Rc 6 (o7 w (Cold.tapes a) k) E H) (j : Nat) (hj : j < 2) :
    E (M7 w a k (Item4.plX a k ⟨225 + j, by omega⟩)) = Gn a r MB Rc 6 (27 + j) := by
  rw [(hWI _ (M7_sc a w _)).1, M7_val, show (Item4.plX a k ⟨225 + j, by omega⟩).val = 132 + Cold.tapes a + 225 + j by
    simp only [Item4.plX]; omega, v7_x (w := w) (k := k) (q98 a k) (q224 a k) (q98_lt a) (q224_lt a) j hj]

theorem st7_bl (w : Nat) (SB : Item4.StartBank a k) (hIn : ∀ j, (SB.inPort j).val = j.val)
    (E : Fin (nW w (Cold.tapes a) k) → List Bool) (H : Fin (nW w (Cold.tapes a) k) → Nat) (hWI : WI a r MB Rc 6 (o7 w (Cold.tapes a) k) E H)
    (x : Fin ((132 + Cold.tapes a) + (373 + k))) (hxin : ∀ j, Item4.plIn SB j ≠ x)
    (h225 : x ≠ Item4.plX a k 225) (h226 : x ≠ Item4.plX a k 226) :
    E (M7 w a k x) = List.replicate Rc false := by
  have hne := q_ne (a := a) (k := k)
  have h98 := q98_lt (a := a) (k := k)
  have h224 := q224_lt (a := a) (k := k)
  rw [(hWI _ (M7_sc a w _)).1, M7_val]
  by_cases e1 : x.val = q98 a k
  · rw [e1, v7_98 (q98 a k) (q224 a k)]; rfl
  by_cases e2 : x.val = q224 a k
  · rw [e2, v7_224 (q98 a k) (q224 a k) hne]; rfl
  by_cases e3 : 132 + Cold.tapes a + 225 ≤ x.val ∧ x.val < 132 + Cold.tapes a + 227
  · exfalso
    by_cases e4 : x.val = 132 + Cold.tapes a + 225
    · exact h225 (Fin.ext (by simp only [Item4.plX]; omega))
    · exact h226 (Fin.ext (by simp only [Item4.plX]; omega))
  by_cases e5 : 132 + Cold.tapes a + 373 ≤ x.val ∧ x.val < 132 + Cold.tapes a + 378
  · exfalso
    exact hxin ⟨x.val - (132 + Cold.tapes a + 373), by omega⟩ (Fin.ext (by rw [plIn_v a SB hIn, Fin.val_mk]; omega))
  have e : v7 w (Cold.tapes a) k (q98 a k) (q224 a k) x.val = o7 w (Cold.tapes a) k + x.val := by
    unfold v7; rw [if_neg e1, if_neg e2, if_neg e3, if_neg e5]
  rw [e]
  exact gn_high (by unfold o7; omega)

/-- The stage-7 invariant step, from the pool run's exported facts. -/
theorem st7_wi (selector : CyclicChoice.Laws) (w : Nat) (SB : Item4.StartBank a k) (hIn : ∀ j, (SB.inPort j).val = j.val)
    (E E' : Fin (nW w (Cold.tapes a) k) → List Bool) (H' : Fin (nW w (Cold.tapes a) k) → Nat)
    (H : Fin (nW w (Cold.tapes a) k) → Nat) (hWI : WI a r MB Rc 6 (o7 w (Cold.tapes a) k) E H)
    (out : ∀ j, H' (M7 w a k (Item4.plOut a k j)) = 0 ∧ E' (M7 w a k (Item4.plOut a k j)) = ZeroPadding.pad Rc
      (BinaryCacheColdRun.input (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) j))
    (ins : ∀ j, E' (M7 w a k (Item4.plIn SB j)) = E (M7 w a k (Item4.plIn SB j)) ∧ H' (M7 w a k (Item4.plIn SB j)) = 0)
    (fr : ∀ x, (∀ y, M7 w a k y ≠ x) → E' x = E x ∧ H' x = H x) :
    WI a r MB Rc 7 (o8 w (Cold.tapes a) k) E' H' := by
  have hne := q_ne (a := a) (k := k)
  have h98 := q98_lt (a := a) (k := k)
  have h224 := q224_lt (a := a) (k := k)
  refine wi_next hWI (by unfold o7 o8; omega) ?_ ?_
  · intro x hx hp
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    have h2 : xv = 25 ∨ xv = 26 := by
      interval_cases xv <;> first | (left; rfl) | (right; rfl) | exact absurd hp (by decide)
    rcases h2 with h2 | h2
    · subst h2
      have ex : (⟨25, hxv⟩ : Fin (nW w (Cold.tapes a) k)) = M7 w a k (Item4.plOut a k 98) :=
        Fin.ext (by rw [M7_val]; exact (v7_98 (q98 a k) (q224 a k)).symm)
      rw [ex]
      exact ⟨(out 98).2, (out 98).1⟩
    · subst h2
      have ex : (⟨26, hxv⟩ : Fin (nW w (Cold.tapes a) k)) = M7 w a k (Item4.plOut a k 224) :=
        Fin.ext (by rw [M7_val]; exact (v7_224 (q98 a k) (q224 a k) hne).symm)
      rw [ex]
      exact ⟨(out 224).2, (out 224).1⟩
  · intro x hx hn
    have hx7 : x.val < 30 ∨ o7 w (Cold.tapes a) k ≤ x.val := by
      rcases hx with h | h
      · left; exact h
      · right; unfold o7 o8 at *; omega
    by_cases hr : ∃ y, M7 w a k y = x
    · obtain ⟨y, hy⟩ := hr
      have hyv : x.val = v7 w (Cold.tapes a) k (q98 a k) (q224 a k) y.val := by rw [← hy, M7_val]
      by_cases e1 : y.val = q98 a k
      · exfalso; apply hn; rw [hyv, e1, v7_98 (q98 a k) (q224 a k)]; exact ⟨by decide, rfl⟩
      by_cases e2 : y.val = q224 a k
      · exfalso; apply hn; rw [hyv, e2, v7_224 (q98 a k) (q224 a k) hne]; exact ⟨by decide, rfl⟩
      by_cases e3 : 132 + Cold.tapes a + 225 ≤ y.val ∧ y.val < 132 + Cold.tapes a + 227
      · have hx27 : x.val = 27 + (y.val - (132 + Cold.tapes a + 225)) := by
          rw [hyv, show y.val = 132 + Cold.tapes a + 225 + (y.val - (132 + Cold.tapes a + 225)) by omega,
            v7_x (w := w) (k := k) (q98 a k) (q224 a k) h98 h224 _ (by omega)]
          omega
        have hold := (hWI x (by omega)).1
        by_cases e4 : y.val = 132 + Cold.tapes a + 225
        · have ey : Item4.plOut a k 225 = y := by
            rw [Item4.plOut_extra (a := a) (k := k) 225 (by decide) (by decide)]
            exact Fin.ext (by simp only [Item4.plX]; omega)
          obtain ⟨o1, o2⟩ := out 225
          rw [ey, hy] at o1 o2
          refine ⟨?_, by rw [o1, (hWI x (by omega)).2]⟩
          rw [o2, hold, cold_input_225 selector a r, show x.val = 27 by omega]
          rfl
        · have ey : Item4.plOut a k 226 = y := by
            rw [Item4.plOut_extra (a := a) (k := k) 226 (by decide) (by decide)]
            exact Fin.ext (by simp only [Item4.plX]; omega)
          obtain ⟨o1, o2⟩ := out 226
          rw [ey, hy] at o1 o2
          refine ⟨?_, by rw [o1, (hWI x (by omega)).2]⟩
          rw [o2, hold, cold_input_226 a r, show x.val = 28 by omega]
          rfl
      by_cases e5 : 132 + Cold.tapes a + 373 ≤ y.val ∧ y.val < 132 + Cold.tapes a + 378
      · have ey : Item4.plIn SB ⟨y.val - (132 + Cold.tapes a + 373), by omega⟩ = y :=
          Fin.ext (by rw [plIn_v a SB hIn, Fin.val_mk]; omega)
        obtain ⟨o1, o2⟩ := ins ⟨y.val - (132 + Cold.tapes a + 373), by omega⟩
        rw [ey, hy] at o1 o2
        exact ⟨o1, by rw [o2, (hWI x hx7).2]⟩
      · exfalso
        have e : v7 w (Cold.tapes a) k (q98 a k) (q224 a k) y.val = o7 w (Cold.tapes a) k + y.val := by
          unfold v7; rw [if_neg e1, if_neg e2, if_neg e3, if_neg e5]
        have := y.isLt
        rw [hyv, e] at hx
        unfold o7 o8 at hx
        omega
    · simp only [not_exists] at hr
      exact fr x hr

theorem st7 (selector : CyclicChoice.Laws) (mask : MaskProducer) (SB : Item4.StartBank a k) (hIn : ∀ j, (SB.inPort j).val = j.val)
    (E : Fin (nW mask.work (Cold.tapes a) k) → List Bool) (H : Fin (nW mask.work (Cold.tapes a) k) → Nat)
    (hWI : WI a r MB Rc 6 (o7 mask.work (Cold.tapes a) k) E H) (hR : SB.need r ≤ Rc) :
    ∃ (H' : Fin (nW mask.work (Cold.tapes a) k) → Nat) (E' : Fin (nW mask.work (Cold.tapes a) k) → List Bool),
      Step (RecoveryFocus.machine (M7 mask.work a k) (Item4.poolBlock SB)) (Item4.poolCost SB r) H E H' E' ∧
      WI a r MB Rc 7 (o8 mask.work (Cold.tapes a) k) E' H' := by
  obtain ⟨H', E', st, out, ins, fr⟩ := Item4.pool_dock selector SB r Rc hR (M7 mask.work a k) (M7_inj a mask.work)
    H E (fun j => (hWI _ (M7_sc a mask.work j)).2) (st7_in a r MB Rc mask.work SB hIn E H hWI)
    (st7_x a r MB Rc mask.work E H hWI 0 (by omega)) (st7_x a r MB Rc mask.work E H hWI 1 (by omega))
    (st7_bl a r MB Rc mask.work SB hIn E H hWI)
  exact ⟨H', E', st, st7_wi a r MB Rc selector mask.work SB hIn E E' H' H hWI out ins fr⟩

/-! ## Stage 8: the child-list length -/

theorem st8 (E : Fin (nW w C k) → List Bool) (H : Fin (nW w C k) → Nat) (hWI : WI a r MB Rc 7 (o8 w C k) E H) :
    ∃ E', Step (RecoveryFocus.machine (m8 w C k) P1Closure.BinaryCacheColdMeasure.machine)
        (P1Closure.BinaryCacheColdMeasure.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs) H E H E' ∧
      WI a r MB Rc 8 (o9 w C k) E' H := by
  have hb : ∀ i, 30 ≤ o8 w C k + i := fun i => by unfold o8; omega
  have sc : ∀ j, (m8 w C k j).val < 30 ∨ o8 w C k ≤ (m8 w C k j).val := by
    intro j; rcases v8_cases w C k j.val with h | h
    · left; exact h
    · right; show o8 w C k ≤ v8 _ _ _ j.val; omega
  have hE : ∀ j, E (m8 w C k j) = Gn a r MB Rc 7 (v8 w C k j.val) := fun j => (hWI _ (sc j)).1
  obtain ⟨E', st, out, fr⟩ := Item4.ms_dock (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs Rc (m8 w C k)
    (m8_inj w C k) H E (fun j => (hWI _ (sc j)).2) (by rw [hE]; rfl) (by rw [hE]; rfl)
    (by
      intro j h0 h12
      rw [hE]
      fin_cases j
      · exact absurd rfl h0
      all_goals first
        | exact absurd rfl h12
        | rfl
        | exact gn_high (hb _))
  refine ⟨E', st, wi_next hWI (by unfold o8 o9; omega) ?_ ?_⟩
  · intro x hx hp
    refine ⟨?_, (hWI x (by omega)).2⟩
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    interval_cases xv <;> first
      | (exact absurd hp (by decide))
      | (exact out)
  · intro x hx hn
    refine ⟨fr x ?_, rfl⟩
    intro j hj
    have hv : v8 w C k j.val = x.val := congrArg Fin.val hj
    rcases v8_cases w C k j.val with h | h
    · fin_cases j
      · left; rfl
      all_goals first
        | (right; rfl)
        | (exfalso; exact hn ⟨hv ▸ h, by rw [← hv]; rfl⟩)
        | (exfalso; exact absurd h (Nat.not_lt.mpr (hb _)))
    · exfalso
      have := j.isLt
      unfold o8 o9 at *
      omega

/-! ## Stages 9–10: the bare meta words -/

theorem st9 (E : Fin (nW w C k) → List Bool) (H : Fin (nW w C k) → Nat) (hWI : WI a r MB Rc 8 (o9 w C k) E H)
    (hMB : MB.length ≤ Rc) :
    ∃ E', Step (RecoveryFocus.machine (m9 w C k) Streaming.machine) (4 * MB.length + 2) H E H E' ∧
      WI a r MB Rc 9 (o10 w C k) E' H := by
  have sc : ∀ j, (m9 w C k j).val < 30 ∨ o9 w C k ≤ (m9 w C k j).val := by
    intro j; rcases v9_cases w C k j.val with h | h
    · left; exact h
    · right; show o9 w C k ≤ v9 _ _ _ j.val; omega
  have hE : ∀ j, E (m9 w C k j) = Gn a r MB Rc 8 (v9 w C k j.val) := fun j => (hWI _ (sc j)).1
  obtain ⟨E', st, out, fr⟩ := Item4.bare_dock (m9 w C k) (m9_inj w C k) H E (fun j => (hWI _ (sc j)).2) Rc MB hMB
    (by rw [hE]; rfl) (by rw [hE]; rfl)
    (by rw [hE]; exact gn_high (show 30 ≤ o9 w C k + 2 by unfold o9; omega))
  refine ⟨E', st, wi_next hWI (by unfold o9 o10; omega) ?_ ?_⟩
  · intro x hx hp
    refine ⟨?_, (hWI x (by omega)).2⟩
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    interval_cases xv <;> first
      | (exact absurd hp (by decide))
      | (exact out)
  · intro x hx hn
    refine ⟨fr x ?_, rfl⟩
    intro j hj h1
    subst h1
    apply hn
    have hv : v9 w C k 1 = x.val := congrArg Fin.val hj
    rw [← hv]
    exact ⟨show (22 : Nat) < 30 by decide, rfl⟩

theorem st10 (E : Fin (nW w C k) → List Bool) (H : Fin (nW w C k) → Nat) (hWI : WI a r MB Rc 9 (o10 w C k) E H)
    (hMB : MB.length ≤ Rc) :
    ∃ E', Step (RecoveryFocus.machine (m10 w C k) Streaming.machine) (4 * (List.replicate MB.length true).length + 2)
        H E H E' ∧ WI a r MB Rc 10 (nW w C k) E' H := by
  have sc : ∀ j, (m10 w C k j).val < 30 ∨ o10 w C k ≤ (m10 w C k j).val := by
    intro j; rcases v10_cases w C k j.val with h | h
    · left; exact h
    · right; show o10 w C k ≤ v10 _ _ _ j.val; omega
  have hE : ∀ j, E (m10 w C k j) = Gn a r MB Rc 9 (v10 w C k j.val) := fun j => (hWI _ (sc j)).1
  obtain ⟨E', st, out, fr⟩ := Item4.bare_dock (m10 w C k) (m10_inj w C k) H E (fun j => (hWI _ (sc j)).2) Rc
    (List.replicate MB.length true) (by rw [List.length_replicate]; exact hMB)
    (by rw [hE]; rfl) (by rw [hE]; rfl)
    (by rw [hE]; exact gn_high (show 30 ≤ o10 w C k + 2 by unfold o10; omega))
  have e := wi_next (s := 9) (lo' := nW w C k) hWI (by unfold o10 nW; omega) (E' := E') (H' := H) ?_ ?_
  · exact ⟨E', st, e⟩
  · intro x hx hp
    refine ⟨?_, (hWI x (by omega)).2⟩
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    interval_cases xv <;> first
      | (exact absurd hp (by decide))
      | (exact out)
  · intro x hx hn
    refine ⟨fr x ?_, rfl⟩
    intro j hj h1
    subst h1
    apply hn
    have hv : v10 w C k 1 = x.val := congrArg Fin.val hj
    rw [← hv]
    exact ⟨show (23 : Nat) < 30 by decide, rfl⟩

end stages

end
end NearCubicWires.SourceFactorSel.Words

