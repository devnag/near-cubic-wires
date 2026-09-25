import Proof.Packets.PacketsCombineThrEngine

/-! # P2 (ii)/(iii): what the two engines compute, in the frozen constructors' own terms

Consumer: `SymCombineStageK`/`ThrCombineStageK` (`Proof/Packets/PacketsRowPolySplitKit.lean`), whose tape-14 word is
the kit register of `(rcDecode a r k).polynomial`; by `rfl` (`PacketsRowPolyPlan.sym_rowPoly`,
`thr_rowPoly`) that is `Normalized.structuralGF2FiniteConjunction (fun i => structuralGF2OneHotLookup …)`
(SYM) or `Normalized.structuralGF2ModularRadixRow p residue 2 coord` (THR). Paper: the row's canonical
polynomial expansion (`paper.tex:1197-1200`); A.13.7 radix tuples (`paper.tex:3113-3142`).

Pure list mathematics (no machine). The radix row's list equation is proved by the recursion
of `structuralGF2FinParity` (`NormalizedFolds.finiteParity_foldr`), then each code's term by the
one-hot selection structure of its table block: the selected bank positions of tuple `t` are
exactly `[0*m + t 0, 1*m + t 1, …]`, in increasing order, so the descending filtered sweep is
`foldr mul acc0 [coord 0 (t 0), coord 1 (t 1), …]` = the finite conjunction.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

/-! ## Block-structured lists -/

theorem flatten_ofFn_getD {α : Type} {N L : ℕ} (f : Fin N → List α) (hL : ∀ c, (f c).length = L)
    (c : Fin N) (p : ℕ) (hp : p < L) (x : α) :
    (List.ofFn f).flatten.getD (c.val * L + p) x = (f c).getD p x := by
  induction N with
  | zero => exact c.elim0
  | succ N ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    by_cases hc : c.val = 0
    · have hc' : c = 0 := Fin.ext hc
      subst hc'
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      rw [List.getD_append _ _ _ _ (by rw [hL]; exact hp)]
    · have hc0 : c ≠ 0 := fun h => hc (by rw [h]; rfl)
      obtain ⟨c', rfl⟩ : ∃ c' : Fin N, c = c'.succ := ⟨c.pred hc0, (Fin.succ_pred c hc0).symm⟩
      have hlen : (f 0).length ≤ c'.succ.val * L + p := by
        rw [hL, Fin.val_succ, Nat.succ_mul]
        omega
      rw [List.getD_append_right _ _ _ _ hlen, hL]
      have e : c'.succ.val * L + p - L = c'.val * L + p := by
        rw [Fin.val_succ, Nat.succ_mul]
        omega
      rw [e]
      exact ih (fun i => f i.succ) (fun i => hL i.succ) c'

theorem flatten_ofFn_length {α : Type} {N L : ℕ} (f : Fin N → List α) (hL : ∀ c, (f c).length = L) :
    (List.ofFn f).flatten.length = N * L := by
  rw [List.length_flatten, List.map_ofFn]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ, List.sum_cons, Function.comp_apply, hL, Nat.succ_mul]
    have := ih (fun i => f i.succ) (fun i => hL i.succ)
    simp only [Function.comp_def] at this ⊢
    omega

/-- A bit-filtered right fold is the right fold over the filtered positions. -/
theorem foldr_ite_filter {α β : Type} (L : List α) (sel : α → Bool) (g : α → β → β) (b : β) :
    L.foldr (fun p acc => if sel p then g p acc else acc) b = (L.filter sel).foldr g b := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases sel p <;> rfl

theorem mul_nil (P : Poly) : Ring.mul P [] = [] := by
  unfold Ring.mul
  induction P with
  | nil => rfl
  | cons m P ih =>
    rw [List.foldl_cons]
    exact ih

theorem foldr_mul_nil (L : List Poly) : L.foldr Ring.mul [] = [] := by
  induction L with
  | nil => rfl
  | cons P L ih => rw [List.foldr_cons, ih, mul_nil]

/-! ## One-hot selection bits of a digit tuple -/

/-- The selection bits of tuple `t`: digit-major, candidate-minor one-hot. -/
def selBits (D m : ℕ) (t : Fin D → Fin m) : List Bool :=
  (List.ofFn (fun d : Fin D => List.ofFn (fun v : Fin m => decide (t d = v)))).flatten

theorem selBits_length (D m : ℕ) (t : Fin D → Fin m) : (selBits D m t).length = D * m :=
  flatten_ofFn_length _ (fun _ => List.length_ofFn)

theorem range_filter_eq (m v : ℕ) (hv : v < m) :
    (List.range m).filter (fun p => decide (p = v)) = [v] := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.filter_append]
    by_cases h : v < m
    · rw [ih h]
      simp; omega
    · have hv' : v = m := by omega
      subst hv'
      have hnil : (List.range v).filter (fun p => decide (p = v)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := List.mem_range.mp ha
        simp; omega
      rw [hnil]
      simp

/-- The selected positions of a tuple, in increasing order. -/
theorem selBits_filter (D m : ℕ) (t : Fin D → Fin m) :
    (List.range (D * m)).filter (fun p => (selBits D m t).getD p false) =
      List.ofFn (fun d : Fin D => d.val * m + (t d).val) := by
  induction D with
  | zero => simp
  | succ D ih =>
    have hsplit : selBits (D + 1) m t =
        List.ofFn (fun v : Fin m => decide (t 0 = v)) ++ selBits D m (fun d => t d.succ) := by
      unfold selBits
      rw [List.ofFn_succ, List.flatten_cons]
    have hlen0 : (List.ofFn (fun v : Fin m => decide (t 0 = v))).length = m := List.length_ofFn
    have h1 : (List.range m).filter (fun p => (selBits (D + 1) m t).getD p false) = [(t 0).val] := by
      have hc : ∀ p ∈ List.range m, (selBits (D + 1) m t).getD p false = decide (p = (t 0).val) := by
        intro p hp
        have hp' := List.mem_range.mp hp
        rw [hsplit, List.getD_append _ _ _ _ (by rw [hlen0]; exact hp')]
        rw [List.getD_eq_getElem _ _ (by rw [hlen0]; exact hp'), List.getElem_ofFn]
        by_cases h : p = (t 0).val
        · subst h; simp
        · have h' : ¬ t 0 = ⟨p, hp'⟩ := fun e => h (by rw [e])
          simp [h, h']
      rw [List.filter_congr hc, range_filter_eq m _ (t 0).isLt]
    have h2 : ((List.range (D * m)).map (fun x => m + x)).filter (fun p => (selBits (D + 1) m t).getD p false) =
        List.ofFn (fun i : Fin D => (i.val + 1) * m + (t i.succ).val) := by
      rw [List.filter_map]
      have hc : ∀ p ∈ List.range (D * m), ((fun p => (selBits (D + 1) m t).getD p false) ∘ (fun x => m + x)) p =
          (selBits D m (fun d => t d.succ)).getD p false := by
        intro p _
        simp only [Function.comp_apply]
        rw [hsplit, List.getD_append_right _ _ _ _ (by rw [hlen0]; omega), hlen0]
        congr 1
        omega
      rw [List.filter_congr hc, ih (fun d => t d.succ), List.map_ofFn]
      congr 1
      funext d
      simp only [Function.comp_apply, Nat.succ_mul]
      omega
    rw [show (D + 1) * m = m + D * m by rw [Nat.succ_mul]; omega, List.range_add, List.filter_append, h1, h2,
      List.ofFn_succ]
    simp

/-! ## THR: the table and the value of one code -/

/-- The THR selection table: per code, its tuple's selection bits then its acceptance bit. -/
def thrTable (D m N : ℕ) (tup : Fin N → Fin D → Fin m) (acc : Fin N → Bool) : List Bool :=
  (List.ofFn (fun c : Fin N => selBits D m (tup c) ++ [acc c])).flatten

theorem thrTable_get (D m N : ℕ) (tup : Fin N → Fin D → Fin m) (acc : Fin N → Bool) (c : Fin N)
    (p : ℕ) (hp : p < D * m) :
    (thrTable D m N tup acc).getD (c.val * (D * m + 1) + p) false = (selBits D m (tup c)).getD p false := by
  unfold thrTable
  rw [flatten_ofFn_getD _ (fun c => by simp [selBits_length]) c p (by omega)]
  rw [List.getD_append _ _ _ _ (by rw [selBits_length]; exact hp)]

theorem thrTable_acc (D m N : ℕ) (tup : Fin N → Fin D → Fin m) (acc : Fin N → Bool) (c : Fin N) :
    (thrTable D m N tup acc).getD (c.val * (D * m + 1) + D * m) false = acc c := by
  unfold thrTable
  rw [flatten_ofFn_getD _ (fun c => by simp [selBits_length]) c (D * m) (by omega)]
  rw [List.getD_append_right _ _ _ _ (by rw [selBits_length]), selBits_length, Nat.sub_self]
  rfl

/-- The filtered sweep over one code's block is the right fold over its selected positions. -/
theorem sweep_filter (ps : List Poly) (D m N : ℕ) (tup : Fin N → Fin D → Fin m) (acc : Fin N → Bool)
    (c : Fin N) (acc0 : Poly) (n : ℕ) :
    sweepAcc ps (thrTable D m N tup acc) (c.val * (D * m + 1)) (D * m) acc0 n =
      ((((List.range (D * m)).drop (D * m - n)).filter (fun p => (selBits D m (tup c)).getD p false)).map
        (fun p => ps.getD p [])).foldr Ring.mul acc0 := by
  unfold sweepAcc fstep
  rw [foldr_ite_filter _ (fun p => (thrTable D m N tup acc).getD (c.val * (D * m + 1) + p) false)
    (fun p acc => Ring.mul (ps.getD p []) acc) acc0, List.foldr_map]
  congr 1
  apply List.filter_congr
  intro p hp
  have hp' := List.mem_range.mp (List.mem_of_mem_drop hp)
  rw [thrTable_get D m N tup acc c p hp']

/-- **One code's term.** -/
theorem codeTerm_eq (ps : List Poly) (D m N : ℕ) (tup : Fin N → Fin D → Fin m) (acc : Fin N → Bool)
    (c : Fin N) :
    codeTerm ps (thrTable D m N tup acc) (D * m) c.val =
      if acc c then Normalized.structuralGF2Product (List.ofFn (fun d : Fin D => ps.getD (d.val * m + (tup c d).val) []))
      else [] := by
  unfold codeTerm
  rw [sweep_filter, Nat.sub_self, List.drop_zero, selBits_filter, List.map_ofFn]
  unfold initAcc
  rw [thrTable_acc]
  cases acc c
  · simp only [Bool.false_eq_true, ite_false]
    exact foldr_mul_nil _
  · rfl

/-- Every partial sweep of a THR table block is a product of at most `D` bank entries. -/
theorem thr_sweep_bounded (S : Finset ℕ) (d : ℕ) (ps : List Poly)
    (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P) (D m N : ℕ) (tup : Fin N → Fin D → Fin m)
    (acc : Fin N → Bool) (c : Fin N) (n : ℕ) :
    NormalizedIntermediate.Bounded S (d * D)
      (sweepAcc ps (thrTable D m N tup acc) (c.val * (D * m + 1)) (D * m)
        (initAcc (thrTable D m N tup acc) (c.val * (D * m + 1)) (D * m)) n) := by
  rw [sweep_filter]
  unfold initAcc
  rw [thrTable_acc]
  have hsub : (((List.range (D * m)).drop (D * m - n)).filter (fun p => (selBits D m (tup c)).getD p false)).Sublist
      (List.ofFn (fun d : Fin D => d.val * m + (tup c d).val)) := by
    rw [← selBits_filter]
    exact (List.drop_sublist _ _).filter _
  have hlen := hsub.length_le
  rw [List.length_ofFn] at hlen
  have hx : ∀ P ∈ (((List.range (D * m)).drop (D * m - n)).filter
      (fun p => (selBits D m (tup c)).getD p false)).map (fun p => ps.getD p []),
      NormalizedIntermediate.Bounded S d P := by
    intro P hP
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hP
    by_cases h : p < ps.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hps _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact NormalizedIntermediate.zero S d
  cases acc c
  · simp only [Bool.false_eq_true, ite_false]
    rw [foldr_mul_nil]
    exact NormalizedIntermediate.zero S _
  · simp only [ite_true]
    have h := NormalizedIntermediate.product _ hx
    apply NormalizedIntermediate.mono h
    rw [List.length_map]
    exact Nat.mul_le_mul_left d hlen

/-! ## The two row polynomials -/

/-- The digit tuple of a code (`finFunctionFinEquiv`, least significant digit first). -/
def tupleOf {D m : ℕ} (c : Fin (m ^ D)) : Fin D → Fin m :=
  (finFunctionFinEquiv : (Fin D → Fin m) ≃ Fin (m ^ D)).symm c

/-- **THR: the engine's parked value is the radix row.** -/
theorem thr_value {pop D : ℕ} (p off : ℕ) (coord : Fin D → Fin (pop + 1) → Poly) :
    (List.ofFn (fun c : Fin ((pop + 1) ^ D) =>
      codeTerm (List.ofFn (fun d : Fin D => List.ofFn (coord d))).flatten
        (thrTable D (pop + 1) ((pop + 1) ^ D) tupleOf
          (fun c => SupplierRadix.modularTupleAccepts p off 2 (tupleOf c))) (D * (pop + 1)) c.val)).foldr
        Ring.add [] =
      Normalized.structuralGF2ModularRadixRow (digits := D) p off 2 coord := by
  unfold Normalized.structuralGF2ModularRadixRow
  rw [NormalizedFolds.finiteParity_foldr]
  congr 1
  apply congrArg List.ofFn
  funext c
  rw [codeTerm_eq]
  have hps : ∀ d : Fin D, (List.ofFn (fun d : Fin D => List.ofFn (coord d))).flatten.getD
      (d.val * (pop + 1) + (tupleOf c d).val) [] = coord d (tupleOf c d) := by
    intro d
    rw [flatten_ofFn_getD _ (fun _ => List.length_ofFn) d _ (tupleOf c d).isLt,
      List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact (tupleOf c d).isLt), List.getElem_ofFn]
  simp only [hps]
  rfl

/-- **SYM: the engine's parked value is the finite conjunction of one-hot lookups.** -/
theorem sym_value {pop n : ℕ} (lookup : Fin n → Fin (pop + 1) → Bool) (coord : Fin n → Fin (pop + 1) → Poly) :
    Normalized.structuralGF2Product (blockPolys (List.ofFn (fun i : Fin n => List.ofFn (coord i))).flatten
      (List.ofFn (fun i : Fin n => List.ofFn (lookup i))).flatten n (pop + 1)) =
      Normalized.structuralGF2FiniteConjunction
        (fun i => Normalized.structuralGF2OneHotLookup (lookup i) (coord i)) := by
  unfold Normalized.structuralGF2FiniteConjunction blockPolys
  congr 1
  apply congrArg List.ofFn
  funext i
  unfold segPoly segTerms
  rw [Normalized.structuralGF2OneHotLookup, NormalizedFolds.finiteParity_foldr]
  congr 1
  apply congrArg List.ofFn
  funext c
  rw [flatten_ofFn_getD _ (fun _ => List.length_ofFn) i c.val c.isLt,
    flatten_ofFn_getD _ (fun _ => List.length_ofFn) i c.val c.isLt,
    List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact c.isLt), List.getElem_ofFn,
    List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact c.isLt), List.getElem_ofFn]
  rfl

end
end NearCubicWires.PacketsCombine
