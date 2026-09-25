import Proof.SourceAssembly.SourceFactorSelWordsLayout

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

/-- The copies stage's five sources: native, support, TOP, `1^q`, `1^K`. -/
def cw (a : DecompositionAlgorithm) (r : Request) : Fin 5 → List Bool :=
  ![r.nativeWord, r.supportWord a, r.topWord a, List.replicate r.q true,
    List.replicate (normalizedLiveCount r.q r.liveScale) true]

theorem gn_new {a : DecompositionAlgorithm} {r : Request} {MB : List Bool} {Rc s p : Nat} (h : s < prod p) :
    Gn a r MB Rc s p = List.replicate Rc false := Gn_new a r MB Rc s p h

theorem gn_high {a : DecompositionAlgorithm} {r : Request} {MB : List Bool} {Rc s p : Nat} (h : 30 ≤ p) :
    Gn a r MB Rc s p = List.replicate Rc false := Gn_high a r MB Rc s p h

section stages
variable {w C k : Nat} (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc : Nat)

/-! ## Stage 1: the copies -/

theorem st1 (E : Fin (nW w C k) → List Bool) (H : Fin (nW w C k) → Nat) (hWI : WI a r MB Rc 0 30 E H)
    (hR : ∀ i, 2 * (cw a r i).length + 1 ≤ Rc) :
    ∃ E', Step (RecoveryFocus.machine (m1 w C k) SourceResident.copiesM) (SourceResident.copiesCost (cw a r)) H E H E' ∧
      WI a r MB Rc 1 43 E' H := by
  have hE : ∀ x : Fin (nW w C k), E x = Gn a r MB Rc 0 x.val := fun x => (hWI x (by omega)).1
  obtain ⟨E', st, out, fr⟩ := SourceResident.copies_run (m1 w C k) (m1_inj w C k) H E
    (fun j => (hWI _ (by omega)).2) (cw a r) (fun _ => Rc) Rc
    (by intro i; rw [hE]; fin_cases i <;> rfl)
    (by
      intro j hj
      rw [hE]
      obtain ⟨jv, hjv⟩ := j
      simp only at hj
      interval_cases jv <;> simp only [m1] <;> first | exact gn_new (by decide) | exact gn_high (by decide))
    hR
  refine ⟨E', st, wi_next hWI (by omega) ?_ ?_⟩
  · intro x hx hp
    refine ⟨?_, (hWI x (by omega)).2⟩
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    interval_cases xv <;> first
      | (exact absurd hp (by decide))
      | (have e := out ⟨0, by decide⟩; exact e)
      | (have e := out ⟨1, by decide⟩; exact e)
      | (have e := out ⟨2, by decide⟩; exact e)
      | (have e := out ⟨3, by decide⟩; exact e)
      | (have e := out ⟨4, by decide⟩; exact e)
      | (have e := out ⟨5, by decide⟩; exact e)
      | (have e := out ⟨6, by decide⟩; exact e)
  · intro x hx hn
    refine ⟨fr x ?_, rfl⟩
    intro j hj
    have hv : v1 j.val = x.val := congrArg Fin.val hj
    rcases v1_cases j.val j.isLt with h | h
    · by_contra hc
      have hj5 : 5 ≤ j.val ∧ j.val ≤ 11 := by omega
      apply hn
      refine ⟨by omega, ?_⟩
      rw [← hv]
      obtain ⟨jv, hjv⟩ := j
      simp only at hj5 ⊢
      obtain ⟨h1, h2⟩ := hj5
      interval_cases jv <;> rfl
    · exfalso; have := j.isLt; omega

/-! ## Stage 2: the occurrence count -/

theorem st2 (E : Fin (nW w C k) → List Bool) (H : Fin (nW w C k) → Nat) (hWI : WI a r MB Rc 1 43 E H)
    (hR : 2 * (r.supportWord a).length + 1 ≤ Rc) :
    ∃ E', Step (RecoveryFocus.machine (m2 w C k) SourceResident.occM)
        (SourceResident.occCost (r.supportWord a).length (r.family a).occurrences.length) H E H E' ∧
      WI a r MB Rc 2 47 E' H := by
  have hE : ∀ x : Fin (nW w C k), (x.val < 30 ∨ 43 ≤ x.val) → E x = Gn a r MB Rc 1 x.val := fun x h => (hWI x h).1
  have sc : ∀ j : Fin 4, (m2 w C k j).val < 30 ∨ 43 ≤ (m2 w C k j).val := by
    intro j; rcases v2_cases j.val j.isLt with h | h
    · left; exact h
    · right; show 43 ≤ v2 j.val; omega
  obtain ⟨E', st, out, fr⟩ := SourceResident.occ_request (m2 w C k) (m2_inj w C k) H E
    (fun j => (hWI _ (sc j)).2) a r Rc Rc Rc
    (by rw [hE _ (sc 0)]; rfl) (by rw [hE _ (sc 1)]; rfl)
    (by rw [hE _ (sc 2)]; rfl) (by rw [hE _ (sc 3)]; rfl) hR
  refine ⟨E', st, wi_next hWI (by omega) ?_ ?_⟩
  · intro x hx hp
    refine ⟨?_, (hWI x (by omega)).2⟩
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    interval_cases xv <;> first
      | (exact absurd hp (by decide))
      | (exact out)
  · intro x hx hn
    refine ⟨fr x ?_, rfl⟩
    intro j hj h2
    subst h2
    apply hn
    have hv : v2 2 = x.val := congrArg Fin.val hj
    rw [← hv]
    exact ⟨by decide, rfl⟩

/-! ## Stage 3: lead ; mask ; frame (the framed mask word) -/

theorem st3 (mask : MaskProducer) (E : Fin (nW mask.work C k) → List Bool) (H : Fin (nW mask.work C k) → Nat)
    (hWI : WI a r MB Rc 2 47 E H)
    (cs : (r.supportWord a).length ≤ Rc) (cq : 4 * r.q + 3 ≤ Rc)
    (ck : 4 * normalizedLiveCount r.q r.liveScale + 3 ≤ Rc) (cm : 4 * (r.family a).occurrences.length + 3 ≤ Rc) :
    ∃ E', Step (RecoveryFocus.machine (m3 mask.work C k) (Item4.lmM mask)) (Item4.lmCost mask a r) H E H E' ∧
      WI a r MB Rc 3 (o4 mask.work) E' H := by
  have hE : ∀ x : Fin (nW mask.work C k), (x.val < 30 ∨ 47 ≤ x.val) → E x = Gn a r MB Rc 2 x.val :=
    fun x h => (hWI x h).1
  have sc : ∀ j : Fin (9 + (5 + mask.work)), (m3 mask.work C k j).val < 30 ∨ 47 ≤ (m3 mask.work C k j).val := by
    intro j; rcases v3_cases j.val with h | h
    · left; exact h
    · right; show 47 ≤ v3 j.val; omega
  obtain ⟨E', st, out, fr⟩ := Item4.lm_dock mask a r Rc (List.replicate (normalizedLiveCount r.q r.liveScale) true)
    (List.replicate (r.family a).occurrences.length true) (List.length_replicate ..) (List.length_replicate ..)
    cs cq (by rw [List.length_replicate]; exact ck) (by rw [List.length_replicate]; exact cm) (by omega)
    (m3 mask.work C k) (m3_inj mask.work C k) H E (fun j => (hWI _ (sc j)).2)
    (by
      intro j
      rw [hE _ (sc j)]
      obtain ⟨jv, hjv⟩ := j
      by_cases h8 : jv < 8
      · interval_cases jv <;> rfl
      · simp only [m3, v3, if_neg h8]
        rw [gn_high (by omega)]
        simp only [show jv ≠ 0 by omega, show jv ≠ 2 by omega, show jv ≠ 3 by omega, show jv ≠ 4 by omega,
          show jv ≠ 5 by omega, ↓reduceIte])
  refine ⟨E', st, wi_next hWI (by simp only [o4]; omega) ?_ ?_⟩
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
    have hv : v3 j.val = x.val := congrArg Fin.val hj
    rcases v3_cases j.val with h | h
    · have h8 : j.val < 8 := by
        by_contra hc; unfold v3 at h; rw [if_neg hc] at h; omega
      obtain ⟨jv, hjv⟩ := j
      simp only at h8 hv h ⊢
      interval_cases jv <;> first
        | decide
        | (exfalso; exact hn ⟨hv ▸ h, by rw [← hv]; rfl⟩)
        | (exfalso; revert h; decide)
    · exfalso
      have := j.isLt
      simp only [o4] at hx
      omega

/-! ## Stage 4: the index block (P's start bank ; the accepted index run) -/

theorem v4_at (w C j : Nat) (hj : j < 7) : v4 w C (132 + C + 4 + j) = t4 w C j := by
  unfold v4; rw [if_pos (by omega)]; congr 1; omega

theorem st4 (mask : MaskProducer) (SB : Item4.StartBank a k) (hIn : ∀ j, (SB.inPort j).val = j.val)
    (E : Fin (nW mask.work (Cold.tapes a) k) → List Bool) (H : Fin (nW mask.work (Cold.tapes a) k) → Nat)
    (hWI : WI a r MB Rc 3 (o4 mask.work) E H) (hR : SB.need r ≤ Rc) :
    ∃ (H' : Fin (nW mask.work (Cold.tapes a) k) → Nat) (E' : Fin (nW mask.work (Cold.tapes a) k) → List Bool),
      Step (RecoveryFocus.machine (m4 mask.work (Cold.tapes a) k) (Item4.idxBlock SB)) (Item4.idxCost SB r) H E H' E' ∧
      WI a r MB Rc 4 (o5 mask.work (Cold.tapes a) k) E' H' := by
  have sc : ∀ j, (m4 mask.work (Cold.tapes a) k j).val < 30 ∨ o4 mask.work ≤ (m4 mask.work (Cold.tapes a) k j).val := by
    intro j; rcases v4_cases mask.work (Cold.tapes a) j.val with h | h
    · left; exact h
    · right; show o4 mask.work ≤ v4 _ _ j.val; omega
  have hE : ∀ j, E (m4 mask.work (Cold.tapes a) k j) = Gn a r MB Rc 3 (v4 mask.work (Cold.tapes a) j.val) :=
    fun j => (hWI _ (sc j)).1
  have hin_v : ∀ j : Fin 5, (Item4.ixIn SB j).val = 132 + Cold.tapes a + 4 + (j.val + 2) := by
    intro j; rw [Item4.ixIn_val, hIn]; omega
  obtain ⟨H', E', st, oH, oA, ins, fr⟩ := Item4.idx_dock SB r Rc hR (m4 mask.work (Cold.tapes a) k)
    (m4_inj mask.work (Cold.tapes a) k) H E (fun j => (hWI _ (sc j)).2)
    (by
      intro j
      rw [hE, hin_v, v4_at _ _ _ (by have := j.isLt; omega)]
      fin_cases j <;> rfl)
    (by
      intro x hx
      rw [hE]
      by_cases hw : 132 + Cold.tapes a + 4 ≤ x.val ∧ x.val < 132 + Cold.tapes a + 11
      · obtain ⟨i, hi⟩ : ∃ i, x.val = 132 + Cold.tapes a + 4 + i := ⟨x.val - (132 + Cold.tapes a + 4), by omega⟩
        have hi7 : i < 7 := by omega
        have hb1 : 30 ≤ o4 mask.work + (132 + Cold.tapes a + 5) := by unfold o4; omega
        rw [hi, v4_at _ _ _ hi7]
        by_cases h2 : 2 ≤ i
        · exfalso
          exact hx ⟨i - 2, by omega⟩ (Fin.ext (by rw [hin_v, hi]; simp only; omega))
        · interval_cases i
          · rfl
          · exact gn_high hb1
      · have e : v4 mask.work (Cold.tapes a) x.val = o4 mask.work + x.val := by unfold v4; rw [if_neg hw]
        rw [e]
        exact gn_high (by unfold o4; omega))
  have hout_v : (m4 mask.work (Cold.tapes a) k (Item4.ixOut a k)).val = 13 := by
    show v4 _ _ (Item4.ixOut a k).val = 13
    rw [Item4.ixOut_val, show 132 + Cold.tapes a + 4 = 132 + Cold.tapes a + 4 + 0 by rfl, v4_at _ _ _ (by omega)]
    rfl
  refine ⟨H', E', st, wi_next hWI (by unfold o4 o5; omega) ?_ ?_⟩
  · intro x hx hp
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    have h13 : xv = 13 := by
      interval_cases xv <;> first | rfl | exact absurd hp (by decide)
    subst h13
    have ex : (⟨13, hxv⟩ : Fin (nW mask.work (Cold.tapes a) k)) = m4 mask.work (Cold.tapes a) k (Item4.ixOut a k) :=
      Fin.ext hout_v.symm
    rw [ex]
    exact ⟨oA, oH⟩
  · intro x hx hn
    by_cases hr : ∃ y, m4 mask.work (Cold.tapes a) k y = x
    · obtain ⟨y, rfl⟩ := hr
      have hyv : (m4 mask.work (Cold.tapes a) k y).val = v4 mask.work (Cold.tapes a) y.val := rfl
      rcases v4_cases mask.work (Cold.tapes a) y.val with h | h
      · have hw : 132 + Cold.tapes a + 4 ≤ y.val ∧ y.val < 132 + Cold.tapes a + 11 := by
          by_contra hc; unfold v4 at h; rw [if_neg hc] at h; unfold o4 at h; omega
        obtain ⟨i, hi⟩ : ∃ i, y.val = 132 + Cold.tapes a + 4 + i := ⟨y.val - (132 + Cold.tapes a + 4), by omega⟩
        have hi7 : i < 7 := by omega
        rw [hi, v4_at _ _ _ hi7] at h
        by_cases h2 : 2 ≤ i
        · have ey : y = Item4.ixIn SB ⟨i - 2, by omega⟩ := Fin.ext (by rw [hin_v, hi]; simp only; omega)
          rw [ey]
          obtain ⟨e1, e2⟩ := ins ⟨i - 2, by omega⟩
          refine ⟨e1, ?_⟩
          rw [e2, (hWI _ (sc _)).2]
        · exfalso
          interval_cases i
          · apply hn
            rw [hyv, hi, v4_at _ _ _ (by omega)]
            exact ⟨show 13 < 30 by decide, rfl⟩
          · revert h; show ¬ (o4 mask.work + (132 + Cold.tapes a + 5) < 30); unfold o4; omega
      · exfalso
        have := y.isLt
        rw [hyv] at hx
        unfold o4 o5 at *
        omega
    · simp only [not_exists] at hr
      exact fr x hr

theorem st5 (mask : MaskProducer) (E : Fin (nW mask.work C k) → List Bool) (H : Fin (nW mask.work C k) → Nat)
    (hWI : WI a r MB Rc 4 (o5 mask.work C k) E H)
    (cs : (r.supportWord a).length ≤ Rc) (cq : 4 * r.q + 3 ≤ Rc)
    (ck : 4 * normalizedLiveCount r.q r.liveScale + 3 ≤ Rc) (cm : 4 * (r.family a).occurrences.length + 3 ≤ Rc)
    (cn : 2 * r.nativeWord.length + 1 ≤ Rc) (cs2 : 2 * (r.supportWord a).length + 1 ≤ Rc)
    (ci : 2 * (r.indexWord a).length + 1 ≤ Rc) (ct : 2 * (r.topWord a).length + 1 ≤ Rc) :
    ∃ E', Step (RecoveryFocus.machine (m5 mask.work C k) (SourceRequest.InputPass.machine mask))
        (SourceRequest.InputPass.cost mask a r) H E H E' ∧
      WI a r MB Rc 5 (o6 mask.work C k) E' H := by
  have sc : ∀ j, (m5 mask.work C k j).val < 30 ∨ o5 mask.work C k ≤ (m5 mask.work C k j).val := by
    intro j; rcases v5_cases mask.work C k j.val with h | h
    · left; exact h
    · right; show o5 mask.work C k ≤ v5 _ _ _ j.val; omega
  have hE : ∀ j, E (m5 mask.work C k j) = Gn a r MB Rc 4 (v5 mask.work C k j.val) := fun j => (hWI _ (sc j)).1
  obtain ⟨E', st, o7, o9, o0, fr⟩ := SourceRequest.InputPass.input_dock mask a r Rc
    (List.replicate (normalizedLiveCount r.q r.liveScale) true)
    (List.replicate (r.family a).occurrences.length true) (List.length_replicate ..) (List.length_replicate ..)
    cs cq (by rw [List.length_replicate]; exact ck) (by rw [List.length_replicate]; exact cm) (by omega) cn cs2 ci ct
    (m5 mask.work C k) (m5_inj mask.work C k) H E (fun j => (hWI _ (sc j)).2)
    (by
      intro j
      rw [hE]
      obtain ⟨jv, hjv⟩ := j
      have hb : ∀ i, 30 ≤ o5 mask.work C k + i := fun i => by unfold o5; omega
      by_cases h16 : jv < 16
      · interval_cases jv <;> first
          | rfl
          | exact gn_high (hb _)
      · have e : v5 mask.work C k jv = o5 mask.work C k + jv := by unfold v5; rw [if_neg h16]
        simp only
        rw [e, gn_high (by unfold o5; omega)]
        simp only [show jv ≠ 3 by omega, show jv ≠ 4 by omega, show jv ≠ 5 by omega, show jv ≠ 6 by omega,
          show jv ≠ 11 by omega, show jv ≠ 12 by omega, show jv ≠ 13 by omega, show jv ≠ 14 by omega,
          show jv ≠ 15 by omega, ↓reduceIte])
  refine ⟨E', st, wi_next hWI (by unfold o5 o6; omega) ?_ ?_⟩
  · intro x hx hp
    refine ⟨?_, (hWI x (by omega)).2⟩
    obtain ⟨xv, hxv⟩ := x
    simp only at hx hp ⊢
    interval_cases xv <;> first
      | (exact absurd hp (by decide))
      | (exact o7)
      | (exact o9)
      | (exact o0)
  · intro x hx hn
    refine ⟨fr x ?_, rfl⟩
    intro j hj
    have hv : v5 mask.work C k j.val = x.val := congrArg Fin.val hj
    rcases v5_cases mask.work C k j.val with h | h
    · have h16 : j.val < 16 := by
        by_contra hc; unfold v5 at h; rw [if_neg hc] at h; unfold o5 at h; omega
      have hb : ∀ i, 30 ≤ o5 mask.work C k + i := fun i => by unfold o5; omega
      obtain ⟨jv, hjv⟩ := j
      simp only at h16 hv h ⊢
      interval_cases jv <;> first
        | decide
        | (exfalso; exact hn ⟨hv ▸ h, by rw [← hv]; rfl⟩)
        | (exfalso; exact absurd h (Nat.not_lt.mpr (hb _)))
    · exfalso
      have := j.isLt
      unfold o5 o6 at *
      omega

end stages

end
end NearCubicWires.SourceFactorSel.Words

