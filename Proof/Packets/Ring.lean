import Proof.Packets.Plan

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open NearCubicWires.SupplierPrinter
open PCJ9eff70d512234a4c_Fixed
open scoped BigOperators

namespace PCJc06b3608d6d34481_Ring
variable {α : Type} [LinearOrder α]

def occ (a : α → Bool) (P : Ring.Poly α) : Nat :=
  (P.map (fun m => (m.all a).toNat)).sum

theorem eval_eq (a : α → Bool) (P : Ring.Poly α) :
    Ring.Eval a P = decide (Odd (occ a P)) := rfl

theorem eval_nil (a : α → Bool) : Ring.Eval a [] = false := by
  simp [eval_eq, occ]

theorem odd_succ (n : Nat) : decide (Odd (1+n)) = !decide (Odd n) := by
  rcases Nat.even_or_odd n with h | h
  · simp [Nat.odd_add, h, Nat.not_odd_iff_even.mpr h]
  · simp [Nat.odd_add, h, Nat.not_even_iff_odd.mpr h]

theorem eval_cons (a : α → Bool) (m : List α) (P : Ring.Poly α) :
    Ring.Eval a (m::P) = ((m.all a) != Ring.Eval a P) := by
  rw [eval_eq, eval_eq]
  change decide (Odd ((m.all a).toNat + occ a P)) = _
  cases h : m.all a
  · simp only [Bool.toNat_false, Nat.zero_add, Bool.false_bne]
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.toNat_true, Bool.true_bne, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not]
    rw [Nat.add_comm, Nat.odd_add_one]

theorem occ_erase (a : α → Bool) {m : List α} {P : Ring.Poly α} (h : m ∈ P) :
    occ a (P.erase m) + (m.all a).toNat = occ a P := by
  have hp := (List.perm_cons_erase h).map (fun n : List α => (n.all a).toNat)
  have hs := hp.sum_eq
  simpa only [occ, List.map_cons, List.sum_cons, Nat.add_comm] using hs.symm

theorem eval_toggle (a : α → Bool) (m : List α) (P : Ring.Poly α) :
    Ring.Eval a (Ring.toggle m P) = ((m.all a) != Ring.Eval a P) := by
  unfold Ring.toggle
  split_ifs with hm
  · rw [eval_eq, eval_eq]
    have h := occ_erase a hm
    cases hb : m.all a
    · simp only [hb, Bool.toNat_false, Nat.add_zero] at h
      simp only [hb, Bool.false_bne]
      rw [h]
    · simp only [hb, Bool.toNat_true] at h
      rw [← h, Nat.add_comm, odd_succ]
      simp [hb]
  · exact eval_cons a m P

theorem eval_foldr (a : α → Bool) (P : Ring.Poly α) :
    Ring.Eval a P = P.foldr (fun m b => m.all a != b) false := by
  induction P with
  | nil => exact eval_nil a
  | cons m P ih => rw [eval_cons, ih, List.foldr_cons]

theorem eval_foldl {β : Type} (a : α → Bool) (g : β → List α) :
    ∀ (l : List β) (acc : Ring.Poly α),
      Ring.Eval a (l.foldl (fun acc x => Ring.toggle (g x) acc) acc) =
        (Ring.Eval a acc != l.foldr (fun x b => (g x).all a != b) false)
  | [], acc => by simp
  | x::l, acc => by
      rw [List.foldl_cons, eval_foldl a g l, eval_toggle, List.foldr_cons]
      cases (g x).all a <;> cases Ring.Eval a acc <;>
        cases l.foldr (fun x b => (g x).all a != b) false <;> rfl

theorem toggle_nodup (m : List α) {P : Ring.Poly α} (h : P.Nodup) :
    (Ring.toggle m P).Nodup := by
  unfold Ring.toggle
  split_ifs with hm
  · exact h.erase m
  · exact List.nodup_cons.mpr ⟨hm,h⟩

theorem foldl_nodup {β : Type} (g : β → List α) :
    ∀ (l : List β) (acc : Ring.Poly α), acc.Nodup →
      (l.foldl (fun acc x => Ring.toggle (g x) acc) acc).Nodup
  | [], _, h => h
  | x::l, acc, h => foldl_nodup g l _ (toggle_nodup _ h)

theorem mem_toggle {m x : List α} {P : Ring.Poly α}
    (h : x ∈ Ring.toggle m P) : x = m ∨ x ∈ P := by
  unfold Ring.toggle at h
  split_ifs at h with hm
  · exact Or.inr (List.mem_of_mem_erase h)
  · exact List.mem_cons.mp h

theorem mem_foldl {β : Type} (g : β → List α) :
    ∀ (l : List β) (acc : Ring.Poly α) {y : List α},
      y ∈ l.foldl (fun acc x => Ring.toggle (g x) acc) acc →
        y ∈ acc ∨ ∃ x ∈ l, y = g x
  | [], _, _, h => Or.inl h
  | x::l, acc, y, h => by
      rcases mem_foldl g l _ h with h | ⟨z,hz,rfl⟩
      · rcases mem_toggle h with rfl | h
        · exact Or.inr ⟨x,List.mem_cons_self,rfl⟩
        · exact Or.inl h
      · exact Or.inr ⟨z,List.mem_cons_of_mem _ hz,rfl⟩

theorem mem_canon {m : List α} {i : α} : i ∈ Ring.canon m ↔ i ∈ m := by
  simp [Ring.canon, List.mem_insertionSort]

theorem canon_all (a : α → Bool) (m : List α) : (Ring.canon m).all a = m.all a := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, mem_canon]

theorem canon_pairwise (m : List α) : (Ring.canon m).Pairwise (· < ·) := by
  have hle : (Ring.canon m).Pairwise (· ≤ ·) :=
    (List.pairwise_insertionSort (· ≤ ·) m).sublist (List.dedup_sublist _)
  have hn : (Ring.canon m).Nodup := List.nodup_dedup _
  exact (hle.and hn).imp (fun h => lt_of_le_of_ne h.1 (by simpa [eq_comm] using h.2))

theorem canon_length (m : List α) : (Ring.canon m).length ≤ m.length := by
  calc (Ring.canon m).length ≤ (m.insertionSort (· ≤ ·)).length :=
      (List.dedup_sublist _).length_le
    _ = m.length := List.length_insertionSort _ _

theorem norm_eval (P : Ring.Poly α) (a : α → Bool) : Ring.Eval a (Ring.norm P) = Ring.Eval a P := by
  unfold Ring.norm
  rw [eval_foldl a Ring.canon P [], eval_nil, Bool.false_bne, eval_foldr a P]
  induction P with
  | nil => rfl
  | cons m P ih => rw [List.foldr_cons, List.foldr_cons, canon_all, ih]

theorem norm_member {P : Ring.Poly α} {m : List α} (hm : m ∈ Ring.norm P) :
    ∃ n ∈ P, m = Ring.canon n := by
  rcases mem_foldl Ring.canon P [] hm with h | h
  · simp at h
  · exact h

theorem norm_normal (P : Ring.Poly α) : Ring.Normal (Ring.norm P) := by
  refine ⟨foldl_nodup Ring.canon P [] List.nodup_nil, ?_⟩
  intro m hm
  obtain ⟨n,_,rfl⟩ := norm_member hm
  exact canon_pairwise n

theorem norm_degree {d : Nat} {P : Ring.Poly α} (h : Ring.Degree d P) :
    Ring.Degree d (Ring.norm P) := by
  intro m hm
  obtain ⟨n,hn,rfl⟩ := norm_member hm
  exact (canon_length n).trans (h n hn)

theorem add_eval (P Q : Ring.Poly α) (a : α → Bool) :
    Ring.Eval a (Ring.add P Q) = (Ring.Eval a P != Ring.Eval a Q) := by
  rw [Ring.add, eval_foldl, eval_foldr a Q]

theorem add_degree {d : Nat} {P Q : Ring.Poly α}
    (hP : Ring.Degree d P) (hQ : Ring.Degree d Q) : Ring.Degree d (Ring.add P Q) := by
  intro m hm
  rcases mem_foldl (fun m => m) Q P hm with h | ⟨n,hn,rfl⟩
  · exact hP m h
  · exact hQ _ hn

theorem mul_inner (a : α → Bool) (m : List α) (Q acc : Ring.Poly α) :
    Ring.Eval a (Q.foldl (fun acc n => Ring.toggle (Ring.canon (m++n)) acc) acc) =
      (Ring.Eval a acc != (m.all a && Ring.Eval a Q)) := by
  rw [eval_foldl, eval_foldr a Q]
  congr 1
  induction Q with
  | nil => cases m.all a <;> rfl
  | cons n Q ih =>
    rw [List.foldr_cons, List.foldr_cons, canon_all, List.all_append, ih]
    cases m.all a <;> cases n.all a <;>
      cases Q.foldr (fun m b => m.all a != b) false <;> rfl

theorem mul_eval (P Q : Ring.Poly α) (a : α → Bool) :
    Ring.Eval a (Ring.mul P Q) = (Ring.Eval a P && Ring.Eval a Q) := by
  unfold Ring.mul
  suffices h : ∀ (l acc : Ring.Poly α),
      Ring.Eval a (l.foldl (fun acc m =>
        Q.foldl (fun acc n => Ring.toggle (Ring.canon (m++n)) acc) acc) acc) =
          (Ring.Eval a acc != (Ring.Eval a l && Ring.Eval a Q)) by
    rw [h P [], eval_nil, Bool.false_bne]
  intro l
  induction l with
  | nil => intro acc; simp [eval_nil]
  | cons m l ih =>
    intro acc
    rw [List.foldl_cons, ih, mul_inner, eval_cons]
    cases m.all a <;> cases Ring.Eval a acc <;> cases Ring.Eval a l <;>
      cases Ring.Eval a Q <;> rfl

theorem mul_degree {d e : Nat} {P Q : Ring.Poly α}
    (hP : Ring.Degree d P) (hQ : Ring.Degree e Q) : Ring.Degree (d+e) (Ring.mul P Q) := by
  unfold Ring.mul
  suffices h : ∀ (l acc : Ring.Poly α), Ring.Degree d l → Ring.Degree (d+e) acc →
      Ring.Degree (d+e) (l.foldl (fun acc m =>
        Q.foldl (fun acc n => Ring.toggle (Ring.canon (m++n)) acc) acc) acc) from
    h P [] hP (by intro m hm; simp at hm)
  intro l
  induction l with
  | nil => intro acc _ h; exact h
  | cons m l ih =>
    intro acc hl hacc
    rw [List.foldl_cons]
    refine ih _ (fun n hn => hl n (List.mem_cons_of_mem _ hn)) ?_
    intro n hn
    rcases mem_foldl (fun n => Ring.canon (m++n)) Q acc hn with hn | ⟨z,hz,rfl⟩
    · exact hacc n hn
    · calc (Ring.canon (m++z)).length ≤ (m++z).length := canon_length _
        _ = m.length+z.length := List.length_append
        _ ≤ d+e := Nat.add_le_add (hl m (List.mem_cons_self)) (hQ z hz)

theorem sum_choose_le (B d : Nat) :
    (∑ h ∈ Finset.range (d+1), Nat.choose B h) ≤ (B+1)^d := by
  have hpow : ∀ d, (∑ h ∈ Finset.range (d+1), B^h) ≤ (B+1)^d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ]
      calc (∑ h ∈ Finset.range (d+1), B^h) + B^(d+1)
          ≤ (B+1)^d+B*(B+1)^d := by
            refine Nat.add_le_add ih ?_
            rw [pow_succ, Nat.mul_comm]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ B) d)
        _ = (B+1)^(d+1) := by rw [pow_succ]; ring
  exact (Finset.sum_le_sum (fun h _ => Nat.choose_le_pow B h)).trans (hpow d)

theorem support_size {d : Nat} {P : Ring.Poly α} (S : Finset α)
    (hN : Ring.Normal P) (hd : Ring.Degree d P)
    (hs : ∀ m ∈ P, ∀ i ∈ m, i ∈ S) : P.length ≤ (S.card+1)^d := by
  classical
  have hinj : ∀ x ∈ P, ∀ y ∈ P, x.toFinset = y.toFinset → x = y := by
    intro x hx y hy he
    exact (hN.2 x hx).eq_of_mem_iff (hN.2 y hy)
      (fun i => by rw [← List.mem_toFinset, he, List.mem_toFinset])
  have hn : (P.map List.toFinset).Nodup := List.Nodup.map_on hinj hN.1
  have hsub : (P.map List.toFinset).toFinset ⊆
      (Finset.range (d+1)).biUnion (fun h => S.powersetCard h) := by
    intro s hs'
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs')
    refine Finset.mem_biUnion.mpr ⟨m.toFinset.card, ?_, ?_⟩
    · have hc : m.toFinset.card ≤ m.length := List.toFinset_card_le m
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hc.trans (hd m hm)))
    · exact Finset.mem_powersetCard.mpr ⟨fun i hi => hs m hm i (List.mem_toFinset.mp hi),rfl⟩
  calc P.length = (P.map List.toFinset).length := (List.length_map _).symm
    _ = (P.map List.toFinset).toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ ≤ ((Finset.range (d+1)).biUnion (fun h => S.powersetCard h)).card := Finset.card_le_card hsub
    _ ≤ ∑ h ∈ Finset.range (d+1), (S.powersetCard h).card := Finset.card_biUnion_le
    _ = ∑ h ∈ Finset.range (d+1), Nat.choose S.card h := by simp only [Finset.card_powersetCard]
    _ ≤ (S.card+1)^d := sum_choose_le S.card d

end PCJc06b3608d6d34481_Ring



set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed

namespace PCJc06b3608d6d34481_Algebra
abbrev P := StructuralGF2Polynomial
abbrev D := RawMonomialDegreeAtMost

@[simp] theorem norm_eval (a : Nat → Bool) (p : P) : evaluateStructuralGF2 a (Ring.norm p) = evaluateStructuralGF2 a p :=
  PCJc06b3608d6d34481_Ring.norm_eval p a
@[simp] theorem add_eval (a : Nat → Bool) (p q : P) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Add p q) = (evaluateStructuralGF2 a p != evaluateStructuralGF2 a q) :=
  PCJc06b3608d6d34481_Ring.add_eval p q a
@[simp] theorem mul_eval (a : Nat → Bool) (p q : P) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Mul p q) = (evaluateStructuralGF2 a p && evaluateStructuralGF2 a q) :=
  PCJc06b3608d6d34481_Ring.mul_eval p q a

theorem product_eval (a : Nat → Bool) (ps : List P) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Product ps) = ps.all (evaluateStructuralGF2 a) := by
  induction ps with
  | nil => simp [Normalized.structuralGF2Product]
  | cons p ps ih =>
    change evaluateStructuralGF2 a (Normalized.structuralGF2Mul p (Normalized.structuralGF2Product ps)) = _
    rw [mul_eval, ih, List.all_cons]

theorem substitute_eval (a : Nat → Bool) (atom : Nat → P) (p : P) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Substitute atom p) =
      evaluateStructuralGF2 (fun c => evaluateStructuralGF2 a (atom c)) p := by
  induction p with
  | nil =>
    change evaluateStructuralGF2 a structuralGF2Zero = evaluateStructuralGF2 _ structuralGF2Zero
    rw [evaluateStructuralGF2_zero, evaluateStructuralGF2_zero]
  | cons m p ih =>
    rw [Normalized.structuralGF2Substitute, add_eval, product_eval, ih]
    change _ = Ring.Eval (fun c => evaluateStructuralGF2 a (atom c)) (m::p)
    rw [PCJc06b3608d6d34481_Ring.eval_cons]
    simp only [List.all_map, Function.comp_def, Ring.Eval, evaluateStructuralGF2]

theorem raw_sum_eval (a : Nat → Bool) (ps : List P) :
    evaluateStructuralGF2 a (structuralGF2Sum ps) = ps.foldr (fun p b => evaluateStructuralGF2 a p != b) false := by
  induction ps with
  | nil => exact evaluateStructuralGF2_zero a
  | cons p ps ih =>
    change evaluateStructuralGF2 a (structuralGF2Add p (structuralGF2Sum ps)) = _
    rw [evaluateStructuralGF2_add, ih, List.foldr_cons]

theorem sum_eval (a : Nat → Bool) (ps : List P) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Sum ps) = ps.foldr (fun p b => evaluateStructuralGF2 a p != b) false := by
  suffices h : ∀ (ps : List P) (acc : P), evaluateStructuralGF2 a (ps.foldl Normalized.structuralGF2Add acc) =
      (evaluateStructuralGF2 a acc != ps.foldr (fun p b => evaluateStructuralGF2 a p != b) false) by
    simpa only [Normalized.structuralGF2Sum, evaluateStructuralGF2_zero, Bool.false_bne]
      using h ps structuralGF2Zero
  intro ps
  induction ps with
  | nil => intro acc; simp
  | cons p ps ih =>
    intro acc
    rw [List.foldl_cons, ih, add_eval, List.foldr_cons]
    cases evaluateStructuralGF2 a p <;> cases evaluateStructuralGF2 a acc <;>
      cases ps.foldr (fun p b => evaluateStructuralGF2 a p != b) false <;> rfl

theorem sum_congr {β : Type} (a : Nat → Bool) (xs : List β) (f g : β → P)
    (h : ∀ x ∈ xs, evaluateStructuralGF2 a (f x) = evaluateStructuralGF2 a (g x)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Sum (xs.map f)) = evaluateStructuralGF2 a (structuralGF2Sum (xs.map g)) := by
  rw [sum_eval, raw_sum_eval]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem parity_congr (a : Nat → Bool) : ∀ {n : Nat} (ps qs : Fin n → P),
    (∀ i, evaluateStructuralGF2 a (ps i) = evaluateStructuralGF2 a (qs i)) →
    evaluateStructuralGF2 a (Normalized.structuralGF2FinParity ps) = evaluateStructuralGF2 a (structuralGF2FinParity qs)
  | 0, ps, qs, _ => rfl
  | n+1, ps, qs, h => by
    rw [Normalized.structuralGF2FinParity, structuralGF2FinParity,
      add_eval, evaluateStructuralGF2_add, h 0,
      parity_congr a (fun i => ps i.succ) (fun i => qs i.succ) (fun i => h i.succ)]

theorem product_congr {β : Type} (a : Nat → Bool) (xs : List β) (f g : β → P)
    (h : ∀ x ∈ xs, evaluateStructuralGF2 a (f x) = evaluateStructuralGF2 a (g x)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Product (xs.map f)) =
      evaluateStructuralGF2 a (structuralGF2Product (xs.map g)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change evaluateStructuralGF2 a (Normalized.structuralGF2Mul (f x)
      (Normalized.structuralGF2Product (xs.map f))) =
      evaluateStructuralGF2 a (structuralGF2Mul (g x) (structuralGF2Product (xs.map g)))
    rw [mul_eval, evaluateStructuralGF2_mul, h x (List.mem_cons_self),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem conjunction_congr (a : Nat → Bool) {n : Nat} (ps qs : Fin n → P)
    (h : ∀ i, evaluateStructuralGF2 a (ps i) = evaluateStructuralGF2 a (qs i)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2FiniteConjunction ps) =
      evaluateStructuralGF2 a (structuralGF2FiniteConjunction qs) := by
  unfold Normalized.structuralGF2FiniteConjunction structuralGF2FiniteConjunction
  simp only [List.ofFn_eq_map]
  exact product_congr a (List.finRange n) ps qs (fun i _ => h i)

theorem norm_degree {d : Nat} {p : P} (h : D d p) : D d (Ring.norm p) :=
  PCJc06b3608d6d34481_Ring.norm_degree h
theorem add_degree {d : Nat} {p q : P} (hp : D d p) (hq : D d q) :
    D d (Normalized.structuralGF2Add p q) := PCJc06b3608d6d34481_Ring.add_degree hp hq
theorem mul_degree {d e : Nat} {p q : P} (hp : D d p) (hq : D e q) :
    D (d+e) (Normalized.structuralGF2Mul p q) := PCJc06b3608d6d34481_Ring.mul_degree hp hq
theorem not_degree {d : Nat} {p : P} (h : D d p) : D d (Normalized.structuralGF2Not p) :=
  add_degree (rawDegree_one d) h

theorem sum_degree {d : Nat} (ps : List P) (h : ∀ p ∈ ps, D d p) :
    D d (Normalized.structuralGF2Sum ps) := by
  suffices hfold : ∀ (ps : List P) (acc : P), (∀ p ∈ ps, D d p) → D d acc →
      D d (ps.foldl Normalized.structuralGF2Add acc) from hfold ps _ h (rawDegree_zero d)
  intro ps
  induction ps with
  | nil => intro acc _ ha; exact ha
  | cons p ps ih =>
    intro acc hp ha
    exact ih _ (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      (add_degree ha (hp p (List.mem_cons_self)))

theorem product_degree (d : Nat) (ps : List P) (h : ∀ p ∈ ps, D d p) :
    D (d*ps.length) (Normalized.structuralGF2Product ps) := by
  induction ps with
  | nil => exact rawDegree_one _
  | cons p ps ih =>
    have hh := mul_degree (h p (List.mem_cons_self))
      (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))
    simpa only [Normalized.structuralGF2Product, List.foldr_cons, List.length_cons,
      Nat.mul_add, Nat.mul_one, Nat.add_comm] using hh

theorem substitute_degree {d : Nat} (atom : Nat → P) (ha : ∀ c, D 1 (atom c))
    (p : P) (hp : D d p) : D d (Normalized.structuralGF2Substitute atom p) := by
  induction p with
  | nil => exact rawDegree_zero _
  | cons m p ih =>
    apply add_degree
    · have hm := product_degree 1 (m.map atom) (by
        intro q hq
        obtain ⟨c,_,rfl⟩ := List.mem_map.mp hq
        exact ha c)
      simp only [List.length_map, Nat.one_mul] at hm
      exact rawDegree_mono hm (hp m (List.mem_cons_self))
    · exact ih (fun n hn => hp n (List.mem_cons_of_mem _ hn))

theorem parity_degree {n d : Nat} (ps : Fin n → P) (h : ∀ i, D d (ps i)) :
    D d (Normalized.structuralGF2FinParity ps) := by
  induction n with
  | zero => exact rawDegree_zero _
  | succ n ih => exact add_degree (h 0) (ih _ (fun i => h i.succ))

theorem conjunction_degree {n d : Nat} (ps : Fin n → P) (h : ∀ i, D d (ps i)) :
    D (n*d) (Normalized.structuralGF2FiniteConjunction ps) := by
  have hh := product_degree d (List.ofFn ps) (by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact h i)
  simpa only [Normalized.structuralGF2FiniteConjunction, List.length_ofFn, Nat.mul_comm] using hh

end PCJc06b3608d6d34481_Algebra

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierRadix NearCubicWires.SupplierTouching
open NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed PCJc06b3608d6d34481_Algebra
namespace PCJc06b3608d6d34481_Degree
theorem rawDegree_elementarySymmetric
    (codes : List ℕ) (degree : ℕ) :
    RawMonomialDegreeAtMost degree
      (Normalized.structuralGF2ElementarySymmetric codes degree) := by
  apply norm_degree
  intro monomial hmonomial
  exact (List.mem_sublistsLen.mp hmonomial).2.le

theorem rawDegree_shiftedElementarySymmetric
    (codes : List ℕ) (offset degree : ℕ) :
    RawMonomialDegreeAtMost degree
      (Normalized.structuralGF2ShiftedElementarySymmetric codes offset degree) := by
  unfold Normalized.structuralGF2ShiftedElementarySymmetric
  apply sum_degree _
  intro polynomial hpolynomial
  obtain ⟨indices, hindices, rfl⟩ := List.mem_map.mp hpolynomial
  apply rawDegree_scale
  intro monomial hmonomial
  have hraw := rawDegree_elementarySymmetric codes indices.1 monomial hmonomial
  have hsplit := List.Nat.mem_antidiagonal.mp hindices
  omega

theorem rawDegree_consecutiveWindowIndicator
    (codes : List ℕ) (offset width target : ℕ) :
    RawMonomialDegreeAtMost width
      (Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target) := by
  unfold Normalized.structuralGF2ConsecutiveWindowIndicator
  apply sum_degree _
  intro polynomial hpolynomial
  obtain ⟨degree, hdegree, rfl⟩ := List.mem_map.mp hpolynomial
  apply rawDegree_scale
  intro monomial hmonomial
  have hraw :=
    rawDegree_shiftedElementarySymmetric codes offset degree monomial hmonomial
  have hdegreeLe := List.mem_range.mp hdegree
  omega

theorem rawDegree_terminalPolynomialVector
    (depth population terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    RawMonomialDegreeAtMost terminalWindow
      (Normalized.structuralTerminalPolynomialVector depth population terminalWindow
        candidate) := by
  unfold Normalized.structuralTerminalPolynomialVector Normalized.structuralTerminalWindowPolynomial
  exact rawDegree_consecutiveWindowIndicator _ 0 terminalWindow candidate.val

theorem rawDegree_deltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (parent child : Fin (population + 1)) :
    RawMonomialDegreeAtMost (2 * window level)
      (Normalized.structuralDeltaFactor label seed window level parent child) := by
  unfold Normalized.structuralDeltaFactor
  dsimp only
  split
  · exact rawDegree_zero _
  · unfold Normalized.structuralDeltaWindowPolynomial
    dsimp only
    exact rawDegree_consecutiveWindowIndicator _ _ _ _

theorem rawDegree_combineListLevel
    {rank depth population childDegree : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population)
    (hchildren : ∀ child,
      RawMonomialDegreeAtMost childDegree (childPolynomials child))
    (parent : Fin (population + 1)) :
    RawMonomialDegreeAtMost (childDegree + 2 * window level)
      (Normalized.structuralCombineListLevel label seed window level childPolynomials
        parent) := by
  unfold Normalized.structuralCombineListLevel
  apply sum_degree _
  intro polynomial hpolynomial
  simp only [List.mem_ofFn] at hpolynomial
  obtain ⟨child, rfl⟩ := hpolynomial
  exact mul_degree (hchildren child)
    (rawDegree_deltaFactor label seed window level parent child)

theorem rawDegree_structuralListPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ)
    (candidate : Fin (population + 1)) :
    RawMonomialDegreeAtMost
      (structuralListCoordinateRawDegreeFrom depth window terminalWindow level)
      (Normalized.structuralListPolynomialVectorFrom label seed window terminalWindow level
        candidate) := by
  rw [Normalized.structuralListPolynomialVectorFrom,
    structuralListCoordinateRawDegreeFrom]
  by_cases hlevel : level < depth
  · rw [dif_pos hlevel, dif_pos hlevel]
    exact rawDegree_combineListLevel label seed window ⟨level, hlevel⟩ _
      (fun child => rawDegree_structuralListPolynomialVectorFrom label seed
        window terminalWindow (level + 1) child) candidate
  · rw [dif_neg hlevel, dif_neg hlevel]
    exact rawDegree_terminalPolynomialVector depth population terminalWindow
      candidate
termination_by depth - level
decreasing_by omega

theorem rawDegree_structuralListPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    RawMonomialDegreeAtMost
      (structuralListCoordinateRawDegree depth window terminalWindow)
      (Normalized.structuralListPolynomialVector label seed window terminalWindow
        candidate) := by
  unfold structuralListCoordinateRawDegree Normalized.structuralListPolynomialVector
  exact rawDegree_structuralListPolynomialVectorFrom label seed window
    terminalWindow 0 candidate

theorem rawDegree_literal {rank depth population : ℕ}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) :
    RawMonomialDegreeAtMost 1 (Normalized.structuralListLiteralAtom (depth := depth) mask label seed code) := by
  have hmask (i : Fin population) : RawMonomialDegreeAtMost 1 (Normalized.structuralMaskedCoordinate mask i) := by
    unfold Normalized.structuralMaskedCoordinate
    split
    · exact rawDegree_variable _
    · exact rawDegree_zero _
  unfold Normalized.structuralListLiteralAtom
  split
  · exact rawDegree_zero _
  · split
    · exact hmask _
    · exact rawDegree_zero _
  · split
    · split
      · exact hmask _
      · exact rawDegree_zero _
    · split
      · exact not_degree (hmask _)
      · exact rawDegree_zero _

theorem rawDegree_masked {rank depth population : ℕ}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (window : Fin depth → ℕ) (terminal : ℕ)
    (candidate : Fin (population+1)) :
    RawMonomialDegreeAtMost (structuralListCoordinateRawDegree depth window terminal)
      (Normalized.structuralMaskedListCoordinate mask label seed window terminal candidate) :=
  substitute_degree _ (rawDegree_literal mask label seed) _
    (rawDegree_structuralListPolynomialVector label seed window terminal candidate)

theorem rawDegree_selector {n d : ℕ} (ps : Fin n → StructuralGF2Polynomial)
    (target : BitInput n) (hp : ∀ i, RawMonomialDegreeAtMost d (ps i)) :
    RawMonomialDegreeAtMost (n*d) (Normalized.structuralGF2BooleanSelector ps target) := by
  have h := product_degree d
    (List.ofFn (fun i => if target i = true then ps i else Normalized.structuralGF2Not (ps i))) (by
      intro P hP
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hP
      split
      · exact hp i
      · exact not_degree (hp i))
  simpa only [Normalized.structuralGF2BooleanSelector,List.length_ofFn,Nat.mul_comm] using h

theorem rawDegree_majority {n d : ℕ} (ps : Fin n → StructuralGF2Polynomial)
    (hp : ∀ i, RawMonomialDegreeAtMost d (ps i)) :
    RawMonomialDegreeAtMost (n*d) (Normalized.structuralGF2BitMajority ps) := by
  unfold Normalized.structuralGF2BitMajority Normalized.structuralGF2TruthTable
  apply parity_degree
  intro code
  split
  · exact rawDegree_selector ps _ hp
  · exact rawDegree_zero _

theorem rawDegree_walk {rank depth population t : ℕ}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminal : ℕ)
    (seed : MargulisWalkSample (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population+1)) :
    RawMonomialDegreeAtMost (t*structuralListCoordinateRawDegree depth window terminal)
      (Normalized.structuralMaskedWalkListCoordinate mask label window terminal seed candidate) :=
  rawDegree_majority _ (fun _ => rawDegree_masked mask label _ window terminal candidate)


end PCJc06b3608d6d34481_Degree

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierRadix NearCubicWires.SupplierTouching
open PCJ9eff70d512234a4c_Fixed PCJc06b3608d6d34481_Algebra
namespace PCJc06b3608d6d34481_Semantic

theorem scale_congr (a : Nat → Bool) (c : ZMod 2) (p q : P) (h : evaluateStructuralGF2 a p = evaluateStructuralGF2 a q) :
    evaluateStructuralGF2 a (structuralGF2Scale c p) = evaluateStructuralGF2 a (structuralGF2Scale c q) := by
  unfold structuralGF2Scale
  split <;> first | rfl | exact h

theorem not_congr (a : Nat → Bool) (p q : P) (h : evaluateStructuralGF2 a p = evaluateStructuralGF2 a q) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Not p) = evaluateStructuralGF2 a (structuralGF2Not q) := by
  unfold Normalized.structuralGF2Not structuralGF2Not
  rw [add_eval, evaluateStructuralGF2_add, h]

theorem ofFn_product_congr (a : Nat → Bool) {n : Nat} (ps qs : Fin n → P)
    (h : ∀ i, evaluateStructuralGF2 a (ps i) = evaluateStructuralGF2 a (qs i)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Product (List.ofFn ps)) =
      evaluateStructuralGF2 a (structuralGF2Product (List.ofFn qs)) :=
  conjunction_congr a ps qs h

theorem ofFn_sum_congr (a : Nat → Bool) {n : Nat} (ps qs : Fin n → P)
    (h : ∀ i, evaluateStructuralGF2 a (ps i) = evaluateStructuralGF2 a (qs i)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2Sum (List.ofFn ps)) =
      evaluateStructuralGF2 a (structuralGF2Sum (List.ofFn qs)) := by
  have hp : List.ofFn ps = (List.finRange n).map ps := List.ofFn_eq_map
  have hq : List.ofFn qs = (List.finRange n).map qs := List.ofFn_eq_map
  rw [hp,hq]
  exact sum_congr a _ ps qs (fun i _ => h i)

theorem lookup_congr (a : Nat → Bool) {n : Nat} (lookup : Fin (n+1) → Bool)
    (ps qs : Fin (n+1) → P) (h : ∀ i, evaluateStructuralGF2 a (ps i) = evaluateStructuralGF2 a (qs i)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2OneHotLookup lookup ps) =
      evaluateStructuralGF2 a (structuralGF2OneHotLookup lookup qs) := by
  apply parity_congr
  intro i
  by_cases hi : lookup i = true <;> simp only [hi, if_true, if_false]
  · exact h i
  · rfl

theorem selector_congr (a : Nat → Bool) {n : Nat} (ps qs : Fin n → P)
    (target : BitInput n) (h : ∀ i, evaluateStructuralGF2 a (ps i) = evaluateStructuralGF2 a (qs i)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2BooleanSelector ps target) =
      evaluateStructuralGF2 a (structuralGF2BooleanSelector qs target) := by
  apply ofFn_product_congr
  intro i
  by_cases hi : target i = true <;> simp only [hi, if_true, if_false]
  · exact h i
  · exact not_congr a _ _ (h i)

theorem majority_congr (a : Nat → Bool) {n : Nat} (ps qs : Fin n → P)
    (h : ∀ i, evaluateStructuralGF2 a (ps i) = evaluateStructuralGF2 a (qs i)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2BitMajority ps) = evaluateStructuralGF2 a (structuralGF2BitMajority qs) := by
  apply parity_congr
  intro i
  by_cases hi : compiledBitMajority (structuralTruthAssignment n i) = true <;>
    simp only [hi, if_true, if_false]
  · exact selector_congr a ps qs _ h
  · rfl

theorem elementary (a : Nat → Bool) (codes : List Nat) (d : Nat) :
    evaluateStructuralGF2 a (Normalized.structuralGF2ElementarySymmetric codes d) =
      evaluateStructuralGF2 a (structuralGF2ElementarySymmetric codes d) := norm_eval _ _

theorem shifted (a : Nat → Bool) (codes : List Nat) (offset d : Nat) :
    evaluateStructuralGF2 a (Normalized.structuralGF2ShiftedElementarySymmetric codes offset d) =
      evaluateStructuralGF2 a (structuralGF2ShiftedElementarySymmetric codes offset d) := by
  apply sum_congr
  intro i _
  exact scale_congr a _ _ _ (elementary a codes i.1)

theorem window (a : Nat → Bool) (codes : List Nat) (offset width target : Nat) :
    evaluateStructuralGF2 a (Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target) =
      evaluateStructuralGF2 a (structuralGF2ConsecutiveWindowIndicator codes offset width target) := by
  apply sum_congr
  intro i _
  exact scale_congr a _ _ _ (shifted a codes offset i)

theorem terminal (a : Nat → Bool) (depth population terminalWindow : Nat)
    (candidate : Fin (population+1)) :
    evaluateStructuralGF2 a (Normalized.structuralTerminalPolynomialVector depth population terminalWindow candidate) =
      evaluateStructuralGF2 a (structuralTerminalPolynomialVector depth population terminalWindow candidate) :=
  window a _ _ _ _

theorem delta (a : Nat → Bool) {rank depth population : Nat}
    (label : Fin population → BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth → Nat) (level : Fin depth) (parent child : Fin (population+1)) :
    evaluateStructuralGF2 a (Normalized.structuralDeltaFactor label seed window level parent child) =
      evaluateStructuralGF2 a (structuralDeltaFactor label seed window level parent child) := by
  unfold Normalized.structuralDeltaFactor structuralDeltaFactor
  dsimp only
  split
  · rename_i h
    simp only [h]
  · rename_i target h
    simp only [h]
    exact PCJc06b3608d6d34481_Semantic.window a _ _ _ _

theorem combine (a : Nat → Bool) {rank depth population : Nat}
    (label : Fin population → BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth → Nat) (level : Fin depth)
    (ps qs : StructuralListPolynomialVector population)
    (h : ∀ i, evaluateStructuralGF2 a (ps i) = evaluateStructuralGF2 a (qs i)) (parent : Fin (population+1)) :
    evaluateStructuralGF2 a (Normalized.structuralCombineListLevel label seed window level ps parent) =
      evaluateStructuralGF2 a (structuralCombineListLevel label seed window level qs parent) := by
  apply ofFn_sum_congr
  intro child
  rw [mul_eval, evaluateStructuralGF2_mul, h child, delta]

theorem vectorFrom (a : Nat → Bool) {rank depth population : Nat}
    (label : Fin population → BinaryVector rank) (seed : ToeplitzSeed rank)
    (window : Fin depth → Nat) (terminalWindow level : Nat) (candidate : Fin (population+1)) :
    evaluateStructuralGF2 a (Normalized.structuralListPolynomialVectorFrom label seed window terminalWindow level candidate) =
      evaluateStructuralGF2 a (structuralListPolynomialVectorFrom label seed window terminalWindow level candidate) := by
  rw [Normalized.structuralListPolynomialVectorFrom, structuralListPolynomialVectorFrom]
  by_cases hl : level < depth
  · rw [dif_pos hl,dif_pos hl]
    exact combine a label seed window ⟨level,hl⟩ _ _
      (fun i => vectorFrom a label seed window terminalWindow (level+1) i) candidate
  · rw [dif_neg hl,dif_neg hl]
    exact terminal a depth population terminalWindow candidate
termination_by depth-level
decreasing_by omega

theorem literal (a : Nat → Bool) {rank depth population : Nat}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : Nat) :
    evaluateStructuralGF2 a (Normalized.structuralListLiteralAtom (depth:=depth) mask label seed code) =
      evaluateStructuralGF2 a (structuralListLiteralAtom (depth:=depth) mask label seed code) := by
  unfold Normalized.structuralListLiteralAtom structuralListLiteralAtom
  cases hd : decodeListLiteralVariable depth population code with
  | none => rfl
  | some v =>
    cases v with
    | terminal coordinate => rfl
    | delta level slot =>
      dsimp only
      cases hs : decodeListLiteralSlot slot with
      | inl coordinate => rfl
      | inr coordinate =>
        dsimp only
        split_ifs
        · exact not_congr a _ _ rfl
        · rfl

theorem masked (a : Nat → Bool) {rank depth population : Nat}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (window : Fin depth → Nat) (terminalWindow : Nat)
    (candidate : Fin (population+1)) :
    evaluateStructuralGF2 a (Normalized.structuralMaskedListCoordinate mask label seed window terminalWindow candidate) =
      evaluateStructuralGF2 a (structuralMaskedListCoordinate mask label seed window terminalWindow candidate) := by
  unfold Normalized.structuralMaskedListCoordinate structuralMaskedListCoordinate
  rw [substitute_eval, evaluateStructuralGF2_substitute]
  have ha : (fun c => evaluateStructuralGF2 a (Normalized.structuralListLiteralAtom (depth:=depth) mask label seed c)) =
      (fun c => evaluateStructuralGF2 a (structuralListLiteralAtom (depth:=depth) mask label seed c)) :=
    funext (fun c => literal a mask label seed c)
  rw [ha]
  exact vectorFrom _ label seed window terminalWindow 0 candidate

theorem walk (a : Nat → Bool) {rank depth population t : Nat}
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank)
    (window : Fin depth → Nat) (terminalWindow : Nat)
    (seed : MargulisWalkSample (2^toeplitzWalkSideBits rank) t) (candidate : Fin (population+1)) :
    evaluateStructuralGF2 a (Normalized.structuralMaskedWalkListCoordinate mask label window terminalWindow seed candidate) =
      evaluateStructuralGF2 a (structuralMaskedWalkListCoordinate mask label window terminalWindow seed candidate) :=
  majority_congr a _ _ (fun _ => masked a mask label _ window terminalWindow candidate)

theorem modular (a : Nat → Bool) {digits populationBound : Nat}
    (modulus offset base : Nat) (ps qs : Fin digits → Fin (populationBound+1) → P)
    (h : ∀ i c, evaluateStructuralGF2 a (ps i c) = evaluateStructuralGF2 a (qs i c)) :
    evaluateStructuralGF2 a (Normalized.structuralGF2ModularRadixRow modulus offset base ps) =
      evaluateStructuralGF2 a (structuralGF2ModularRadixRow modulus offset base qs) := by
  apply parity_congr
  intro code
  dsimp only
  split
  · exact conjunction_congr a _ _ (fun i => h i _)
  · rfl

end PCJc06b3608d6d34481_Semantic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierTouching
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter NearCubicWires.SupplierRadix
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed PCJc06b3608d6d34481_Algebra
namespace PCJc06b3608d6d34481_Rows

theorem coordinate_degree {q : Nat} (occ : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (den : Nat) (mask : Finset (Fin occ.length))
    (sample : LiveRows.Seed occ I den) (candidate : Fin (occ.length+1)) :
    D (Packets.coordinateDegree occ I den) (LiveRows.coordinatePoly true occ I den mask sample candidate) :=
  PCJc06b3608d6d34481_Degree.rawDegree_walk mask _ _ _ sample candidate

theorem coordinate_eval (assignment : Nat → Bool) {q : Nat} (occ : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (den : Nat) (mask : Finset (Fin occ.length))
    (sample : LiveRows.Seed occ I den) (candidate : Fin (occ.length+1)) :
    evaluateStructuralGF2 assignment (LiveRows.coordinatePoly true occ I den mask sample candidate) =
      evaluateStructuralGF2 assignment (LiveRows.coordinatePoly false occ I den mask sample candidate) :=
  PCJc06b3608d6d34481_Semantic.walk assignment mask _ _ _ sample candidate

theorem sym_degree (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (den : Nat) (sample : LiveRows.Seed (symmetricFourfoldOccurrences r) I den)
    (offset : Fin r.circuits.length → Nat) :
    D (r.circuits.length * Packets.coordinateDegree (symmetricFourfoldOccurrences r) I den)
      (LiveRows.symPolynomial true r I den sample offset) := by
  apply conjunction_degree
  intro i
  apply parity_degree
  intro candidate
  split
  · exact coordinate_degree _ I den _ sample candidate
  · exact rawDegree_zero _

theorem sym_eval (assignment : Nat → Bool) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (den : Nat) (sample : LiveRows.Seed (symmetricFourfoldOccurrences r) I den)
    (offset : Fin r.circuits.length → Nat) :
    evaluateStructuralGF2 assignment (LiveRows.symPolynomial true r I den sample offset) =
      evaluateStructuralGF2 assignment (LiveRows.symPolynomial false r I den sample offset) := by
  apply conjunction_congr
  intro i
  apply PCJc06b3608d6d34481_Semantic.lookup_congr
  exact coordinate_eval assignment _ I den _ sample

theorem thr_degree (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (I : Finset (Fin r.q)) (den : Nat) (sel : ThresholdRows.Selection a r) (p offset : Nat)
    (sample : LiveRows.Seed (thresholdFourfoldOccurrences r) I den) :
    D (modulusDigitCount p * Packets.coordinateDegree (thresholdFourfoldOccurrences r) I den)
      (LiveRows.thrPolynomial true a r I den sel p offset sample) := by
  apply parity_degree
  intro code
  dsimp only
  split
  · apply conjunction_degree
    intro digit
    exact coordinate_degree _ I den _ sample _
  · exact rawDegree_zero _

theorem thr_eval (assignment : Nat → Bool) (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (I : Finset (Fin r.q)) (den : Nat) (sel : ThresholdRows.Selection a r) (p offset : Nat)
    (sample : LiveRows.Seed (thresholdFourfoldOccurrences r) I den) :
    evaluateStructuralGF2 assignment (LiveRows.thrPolynomial true a r I den sel p offset sample) =
      evaluateStructuralGF2 assignment (LiveRows.thrPolynomial false a r I den sel p offset sample) := by
  apply PCJc06b3608d6d34481_Semantic.modular
  intro digit candidate
  exact coordinate_eval assignment _ I den _ sample candidate

theorem rows : PCJc06b3608d6d34481_Plan.RowFacts := by
  intro sources L target mode q circuit pcpp atoms r hr
  cases mode with
  | false =>
    change r ∈ (Packets.thrFamily (decompositionOf sources)
      ⟨q,atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩ L target).rows at hr
    obtain ⟨sel,_,hp⟩ := List.mem_flatMap.mp hr
    obtain ⟨p,_,he⟩ := List.mem_flatMap.mp hp
    obtain ⟨e,_,ho⟩ := List.mem_flatMap.mp he
    obtain ⟨offset,_,rfl⟩ := List.mem_map.mp ho
    exact ⟨thr_degree _ _ _ _ sel p.val offset.val e,
      fun assignment => thr_eval assignment _ _ _ _ sel p.val offset.val e⟩
  | true =>
    change r ∈ (Packets.symFamily
      ⟨q,atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩ L target).rows at hr
    obtain ⟨e,_,ho⟩ := List.mem_flatMap.mp hr
    obtain ⟨offset,_,rfl⟩ := List.mem_map.mp ho
    exact ⟨sym_degree _ _ _ e offset, fun assignment => sym_eval assignment _ _ _ e offset⟩

end PCJc06b3608d6d34481_Rows

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierTouching
open NearCubicWires.SupplierPrinter NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed PCJc06b3608d6d34481_Algebra
namespace PCJc06b3608d6d34481_Transport
open C10SupplierRowInput

theorem lowered_degree {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (r : Packets.Row F.occurrences L) (h : Ring.Degree r.degree r.polynomial) :
    Ring.Degree r.degree (Packets.lowered a F r) :=
  substitute_degree _ (fun c => norm_degree (CloseoutRowsUniversal.atom_degree a _ _ c)) _ h

theorem lowered_eval {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (r : Packets.Row F.occurrences L) (x : BitInput q) :
    evaluateStructuralGF2 (CloseoutRowsUniversal.assignment a (Packets.live F) F.occurrences x) (Packets.lowered a F r) =
      evaluateStructuralGF2 (LiveRows.residualAssignment F.occurrences (Packets.live F) x) r.polynomial := by
  unfold Packets.lowered
  rw [substitute_eval]
  have ha : (fun c => evaluateStructuralGF2 (CloseoutRowsUniversal.assignment a (Packets.live F) F.occurrences x)
      (Ring.norm (CloseoutRowsUniversal.atomOfCode a (Packets.live F) F.occurrences c))) =
      (fun c => evaluateStructuralGF2 (CloseoutRowsUniversal.assignment a (Packets.live F) F.occurrences x)
        (CloseoutRowsUniversal.atomOfCode a (Packets.live F) F.occurrences c)) :=
    funext (fun c => norm_eval _ _)
  rw [ha, ← evaluateStructuralGF2_substitute]
  exact CloseoutRowsUniversal.lower_value a _ _ _ x

theorem transport : PCJc06b3608d6d34481_Plan.PacketTransport := by
  intro q L a F g r hr
  classical
  have hl : Ring.Degree r.degree (Packets.lowered a F r) := lowered_degree a F r hr.1
  constructor
  · intro yi
    let f : Nat → Fin (Packets.pool a F g).length := fun code =>
      Fin.cast (BinaryPool.pool_length a (Packets.live F) F.occurrences (Packets.residual F) g.arity).symm
        (poolIndex a (Packets.live F) F.occurrences (Packets.residual F) g.arity yi code)
    let M := (childList a (Packets.live F) F.occurrences).length
    let S : Finset (Fin (Packets.pool a F g).length) := insert (f M) ((Finset.range M).image f)
    have hf (c : Nat) : f c ∈ S := by
      by_cases hc : c < M
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c,Finset.mem_range.mpr hc,rfl⟩)
      · have he : f c = f M := by
          apply Fin.ext
          simp only [f, Fin.val_cast, poolIndex, show ¬ c < (childList a (Packets.live F) F.occurrences).length from hc,
            dif_neg, dite_false, show ¬ M < (childList a (Packets.live F) F.occurrences).length from Nat.lt_irrefl M]
        rw [he]
        exact Finset.mem_insert_self _ _
    have hcard : S.card ≤ M+1 := by
      calc S.card ≤ ((Finset.range M).image f).card+1 := Finset.card_insert_le _ _
        _ ≤ (Finset.range M).card+1 := Nat.add_le_add_right Finset.card_image_le 1
        _ = M+1 := by rw [Finset.card_range]
    have hn : Ring.Normal (Packets.one a F g r yi) := PCJc06b3608d6d34481_Ring.norm_normal _
    have hd : Ring.Degree r.degree (Packets.one a F g r yi) := by
      apply PCJc06b3608d6d34481_Ring.norm_degree
      intro m hm
      obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hm
      simpa only [List.length_map] using hl n hn
    refine ⟨hn,hd,?_⟩
    have hs : ∀ m ∈ Packets.one a F g r yi, ∀ i ∈ m, i ∈ S := by
      intro m hm i hi
      obtain ⟨n,hn,rfl⟩ := PCJc06b3608d6d34481_Ring.norm_member hm
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hn
      have hi' := PCJc06b3608d6d34481_Ring.mem_canon.mp hi
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp hi'
      exact hf c
    exact (PCJc06b3608d6d34481_Ring.support_size S hn hd hs).trans
      (Nat.pow_le_pow_left (by change S.card+1 ≤ M+2; omega) r.degree)
  · intro yi x
    unfold Packets.one
    rw [PCJc06b3608d6d34481_Ring.norm_eval]
    unfold Ring.Eval
    rw [exactPolynomialValue_map]
    have he : (fun c (_ : Unit) (_ : Unit) =>
        ((Packets.pool a F g).get
          (Fin.cast (BinaryPool.pool_length a (Packets.live F) F.occurrences (Packets.residual F) g.arity).symm
            (poolIndex a (Packets.live F) F.occurrences (Packets.residual F) g.arity yi c))).eval x) =
        (fun c (_ : Unit) (_ : Unit) => CloseoutRowsUniversal.assignment a (Packets.live F) F.occurrences
          (joinInput (Packets.live F) (BinaryPool.assignmentAt (Packets.live F) yi.val)
            (residualPoint (Packets.live F) (Packets.residual F) g.arity x)) c) := by
      funext c _ _
      exact BinaryPool.pool_index_eval a _ _ _ g.arity yi c x
    rw [he]
    change evaluateStructuralGF2 _ (Packets.lowered a F r) = _
    rw [lowered_eval]
    exact hr.2 _

end PCJc06b3608d6d34481_Transport

