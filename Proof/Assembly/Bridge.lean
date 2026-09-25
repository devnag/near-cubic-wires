import Proof.Assembly.State

/-! Semantic bridge for the cyclic-mask producer (plan §12.3): the doubled
window read at head `q-j` is the indicator of `CyclicChoice.window q K j`, and
the kept count at that head plus the incidence score at `j` is `m*K`. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Bridge
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
open PCJc4297ab269d8423a_Source
open PCJ9eff70d512234a4c_Fixed
open scoped BigOperators

/-- The literal slice the decision copies; the same expression as `Window.slice`. -/
def slice (d : MaskData) (i : Nat) : List Bool := ((State.double d).drop (d.q-i)).take d.q

theorem double_length (d : MaskData) : (State.double d).length = 2*d.q := by
  simp [State.double]; omega

theorem double_getD (d : MaskData) (k : Nat) (hk : k < 2*d.q) :
    (State.double d).getD k false = decide (k % d.q < d.K) := by
  have hlen := double_length d
  rw [List.getD_eq_getElem _ _ (by omega)]
  unfold State.double
  by_cases h : k < d.q
  · rw [List.getElem_append_left (by simpa using h)]
    simp [Init.bits, Nat.mod_eq_of_lt h]
  · rw [List.getElem_append_right (by simpa using h)]
    have hm : k % d.q = k - d.q := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Init.bits, hm]

theorem mem_window {q K start : Nat} (x : Fin q) :
    x ∈ CyclicChoice.window q K start ↔ (x.val + q - start % q) % q < K := by
  simp [CyclicChoice.window]

/-- Reading the doubled mask at head `q-j` position `x` is membership in window `j`. -/
theorem double_window (d : MaskData) (j : Nat) (hj : j < d.q) (x : Fin d.q) :
    readTapeBit (State.double d) (d.q-j+x) = decide (x ∈ CyclicChoice.window d.q d.K j) := by
  unfold readTapeBit
  rw [double_getD d _ (by omega)]
  rw [show decide (x ∈ CyclicChoice.window d.q d.K j) =
      decide ((x.val + d.q - j % d.q) % d.q < d.K) from decide_eq_decide.mpr (mem_window x)]
  rw [Nat.mod_eq_of_lt hj]
  have he : (d.q-j+x.val) % d.q = (x.val+d.q-j) % d.q := by congr 1; omega
  rw [he]

theorem slice_length (d : MaskData) (j : Nat) (hj : j < d.q) : (slice d j).length = d.q := by
  simp [slice, double_length]; omega

/-- Item 1 of §12.3: the slice at head `q-j` is the indicator of window `j`. -/
theorem slice_eq (d : MaskData) (j : Nat) (hj : j < d.q) :
    slice d j = List.ofFn (fun x : Fin d.q => decide (x ∈ CyclicChoice.window d.q d.K j)) := by
  apply List.ext_getElem
  · rw [slice_length d j hj, List.length_ofFn]
  · intro x hx1 hx2
    have hx : x < d.q := by rw [slice_length d j hj] at hx1; exact hx1
    rw [List.getElem_ofFn]
    simp only [slice, List.getElem_take, List.getElem_drop]
    rw [← List.getD_eq_getElem]
    exact double_window d j hj ⟨x,hx⟩

theorem foldl_fst (mask : Fin 3 → List Bool) (j : Nat) (rs : List (List Bool)) (s : Rows.Score) :
    (rs.foldl (Rows.next mask j) s).1 = s.1 + (rs.map (fun bs => count (Scan.cells mask j bs))).sum := by
  induction rs generalizing s with
  | nil => simp
  | cons bs rs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    simp only [Rows.next]
    omega

theorem count_ofFn (d : MaskData) : ∀ {n : Nat} (off : Nat) (f : Fin n → Bool),
    count (Scan.cells (State.masks d) off (List.ofFn f)) =
      ∑ x : Fin n, (readTapeBit (State.double d) (off+x) && !f x).toNat
  | 0, off, f => by simp [Scan.cells, count]
  | n+1, off, f => by
    rw [List.ofFn_succ, Scan.cells, count, Fin.sum_univ_succ, count_ofFn d (off+1)]
    have hk : kept (f 0, readTapeBit (State.masks d 0) off, readTapeBit (State.masks d 1) off,
        readTapeBit (State.masks d 2) off) = (readTapeBit (State.double d) off && !f 0) := by
      simp [kept, State.masks]
    rw [hk]
    have hz : (readTapeBit (State.double d) (off + ((0 : Fin (n+1)) : Nat)) && !f 0) =
        (readTapeBit (State.double d) off && !f 0) := by simp
    rw [hz]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [Fin.val_succ]
    rw [show off + 1 + x.val = off + (x.val + 1) by omega]

theorem count_add_incidence {q : Nat} (W S : Finset (Fin q)) :
    (∑ x : Fin q, (decide (x ∈ W) && !decide (x ∈ S)).toNat) +
      (∑ x ∈ S, if x ∈ W then 1 else 0) = W.card := by
  classical
  have h2 : (∑ x : Fin q, if x ∈ S then (if x ∈ W then 1 else 0) else 0) =
      ∑ x ∈ S, if x ∈ W then 1 else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [← h2, ← Finset.sum_add_distrib]
  have h3 : ∀ x : Fin q, (decide (x ∈ W) && !decide (x ∈ S)).toNat +
      (if x ∈ S then (if x ∈ W then 1 else 0) else 0) = if x ∈ W then 1 else 0 := by
    intro x
    by_cases hW : x ∈ W <;> by_cases hS : x ∈ S <;> simp [hW, hS]
  rw [Finset.sum_congr rfl (fun x _ => h3 x), Finset.sum_boole]
  simp

theorem window_card_pos {q : Nat} (K j : Nat) (hq : 0 < q) (hK : K ≤ q) :
    (CyclicChoice.window q K j).card = K := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  let c : Fin q := ⟨(q - j % q) % q, Nat.mod_lt _ hq⟩
  have hW : CyclicChoice.window q K j =
      (Finset.univ.filter (fun y : Fin q => y.val < K)).map (Equiv.addRight c).symm.toEmbedding := by
    ext x
    rw [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter, mem_window]
    simp only [Finset.mem_univ, true_and, Equiv.coe_addRight, Fin.val_add]
    have hj : j % q < q := Nat.mod_lt _ hq
    have he : (x.val + q - j % q) % q = (x.val + c.val) % q := by
      show _ = (x.val + (q - j % q) % q) % q
      rw [Nat.add_mod_mod]
      congr 1
      set t := j % q with ht
      omega
    rw [he]
  rw [hW, Finset.card_map]
  have := Fin.card_filter_val_lt (n := q) (m := K)
  simpa [min_eq_right hK] using this

theorem window_card {q : Nat} (K j : Nat) (hK : K ≤ q) :
    (CyclicChoice.window q K j).card = K := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have : K = 0 := by omega
    subst this
    simp [CyclicChoice.window]
  · exact window_card_pos K j hq hK

/-- Item 2 of §12.3: kept count at head `q-j` plus incidence at `j` is `m*K`. -/
theorem score_eq (d : MaskData) (j : Nat) (hj : j < d.q) :
    (State.result d (d.q-j)).1 + CyclicChoice.incidenceScore d.support d.K j = d.m * d.K := by
  classical
  unfold State.result CyclicChoice.incidenceScore
  rw [foldl_fst, State.rows, List.map_ofFn, List.sum_ofFn]
  simp only [Nat.zero_add, Function.comp]
  rw [← Finset.sum_add_distrib]
  have hrow : ∀ i : Fin d.m,
      count (Scan.cells (State.masks d) (d.q-j) (List.ofFn (fun x : Fin d.q => decide (x ∈ d.support i)))) +
        (∑ x ∈ d.support i, if x ∈ CyclicChoice.window d.q d.K j then 1 else 0) = d.K := by
    intro i
    rw [count_ofFn]
    have hc : ∀ x : Fin d.q, (readTapeBit (State.double d) (d.q-j+x) && !decide (x ∈ d.support i)).toNat =
        (decide (x ∈ CyclicChoice.window d.q d.K j) && !decide (x ∈ d.support i)).toNat := by
      intro x; rw [double_window d j hj x]
    rw [Finset.sum_congr rfl (fun x _ => hc x), count_add_incidence, window_card _ _ d.bound]
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  simp

end PCJ93d4cfe17dc847a3.Bridge
