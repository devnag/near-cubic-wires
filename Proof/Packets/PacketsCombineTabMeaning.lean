import Proof.Packets.PacketsCombineMeaning

/-! # P2 (iii) table writer, part 0: the THR selection table as digit-list mathematics

Consumer: `ThrMeta` (`Proof/Packets/PacketsCombineThrLocal.lean`) must leave the selection table `thrTableOf` =
`thrTable digits (pop+1) N tupleOf (fun c => modularTupleAccepts prime residue 2 (tupleOf c))` on its
tape 15. Paper: A.13.7 (`paper.tex:3113-3142`): the modular radix row ranges over every digit tuple
`Fin ((pop+1)^digits)` accepted by `modularTupleAccepts`; the tuples are internal preprocessing of the
row, charged in `T_prep` (`paper.tex:1197-1200`).

Pure list mathematics, no machine. The table writer enumerates the codes with an odometer on the
one-hot tuple blocks (`incr_digitsOf`: one increment of the little-endian digit list is the next code)
and decides acceptance by a gated sum of per-cell weights `v * 2^d` (`gsum_blocks`: on a one-hot
block list it is the base-two radix value). `tabPrefix_full` identifies the writer's row-by-row output
with the consumer's `thrTable`.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine

/-! ## One-hot blocks of digit lists -/

/-- The one-hot block of width `m` of digit `x`. -/
def oneHot (m x : ℕ) : List Bool := List.ofFn (fun v : Fin m => decide (x = v.val))

/-- The one-hot blocks of a little-endian digit list. -/
def blocksOf (m : ℕ) (ds : List ℕ) : List Bool := (ds.map (oneHot m)).flatten

/-- The `D` little-endian base-`m` digits of `c`. -/
def digitsOf (m : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | D + 1, c => c % m :: digitsOf m D (c / m)

/-- The odometer increment of a little-endian digit list (wrapping at `m`). -/
def incr (m : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: ds => if x + 1 < m then (x + 1) :: ds else 0 :: incr m ds

theorem oneHot_length (m x : ℕ) : (oneHot m x).length = m := List.length_ofFn

theorem blocksOf_cons (m x : ℕ) (ds : List ℕ) : blocksOf m (x :: ds) = oneHot m x ++ blocksOf m ds := by
  simp only [blocksOf, List.map_cons, List.flatten_cons]

theorem blocksOf_length (m : ℕ) (ds : List ℕ) : (blocksOf m ds).length = ds.length * m := by
  induction ds with
  | nil => simp [blocksOf]
  | cons x ds ih =>
    rw [blocksOf_cons, List.length_append, oneHot_length, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem digitsOf_length (m D c : ℕ) : (digitsOf m D c).length = D := by
  induction D generalizing c with
  | zero => rfl
  | succ D ih => simp only [digitsOf, List.length_cons, ih]

theorem digitsOf_lt (m : ℕ) (hm : 1 ≤ m) (D c : ℕ) : ∀ x ∈ digitsOf m D c, x < m := by
  induction D generalizing c with
  | zero => intro x hx; simp [digitsOf] at hx
  | succ D ih =>
    intro x hx
    simp only [digitsOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by omega)
    · exact ih _ x hx

/-- **One odometer increment is the next code.** -/
theorem incr_digitsOf (m : ℕ) (hm : 1 ≤ m) (D : ℕ) : ∀ c, incr m (digitsOf m D c) = digitsOf m D (c + 1) := by
  induction D with
  | zero => intro c; rfl
  | succ D ih =>
    intro c
    simp only [digitsOf, incr]
    have hlt : c % m < m := Nat.mod_lt _ (by omega)
    have e : c + 1 = (c % m + 1) + m * (c / m) := by rw [Nat.add_right_comm, Nat.mod_add_div]
    by_cases h : c % m + 1 < m
    · rw [if_pos h]
      have h1 : (c + 1) % m = c % m + 1 := by
        rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
      have h2 : (c + 1) / m = c / m := by
        rw [e, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]
      rw [h1, h2]
    · rw [if_neg h, ih]
      have hcm : c % m + 1 = m := by omega
      have e2 : c + 1 = m * (c / m + 1) := by
        rw [e, hcm, Nat.mul_add, Nat.mul_one, Nat.add_comm]
      have h1 : (c + 1) % m = 0 := by rw [e2, Nat.mul_mod_right]
      have h2 : (c + 1) / m = c / m + 1 := by rw [e2, Nat.mul_div_cancel_left _ (by omega)]
      rw [h1, h2]

theorem digitsOf_eq_ofFn (m D : ℕ) : ∀ c, digitsOf m D c = List.ofFn (fun d : Fin D => c / m ^ d.val % m) := by
  induction D with
  | zero => intro c; rfl
  | succ D ih =>
    intro c
    rw [List.ofFn_succ]
    simp only [digitsOf, Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ]
    rw [ih]
    congr 1
    apply congrArg List.ofFn
    funext d
    rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- The consumer's selection bits of a code are the one-hot blocks of its digit list. -/
theorem selBits_tupleOf (D m : ℕ) (c : Fin (m ^ D)) :
    selBits D m (tupleOf c) = blocksOf m (digitsOf m D c.val) := by
  rw [digitsOf_eq_ofFn, blocksOf, List.map_ofFn, selBits]
  congr 1
  apply congrArg List.ofFn
  funext d
  simp only [Function.comp_apply, oneHot]
  apply congrArg List.ofFn
  funext v
  exact decide_eq_decide.mpr Fin.ext_iff

/-! ## The radix value as a gated sum of cell weights -/

/-- The base-two radix value of a little-endian digit list, place `e` first. -/
def radixList : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: ds, e => x * 2 ^ e + radixList ds (e + 1)

theorem radixValue_tupleOf (D pop : ℕ) (c : Fin ((pop + 1) ^ D)) :
    SupplierRadix.radixValue 2 (tupleOf c) = radixList (digitsOf (pop + 1) D c.val) 0 := by
  let m := pop + 1
  have key : ∀ (D : ℕ) (c e : ℕ),
      (∑ d : Fin D, 2 ^ (e + d.val) * (c / m ^ d.val % m)) = radixList (digitsOf m D c) e := by
    intro D
    induction D with
    | zero => intro c e; simp [digitsOf, radixList]
    | succ D ih =>
      intro c e
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.add_zero, pow_zero, Nat.div_one, Fin.val_succ, digitsOf, radixList]
      rw [← ih (c / m) (e + 1)]
      have hs : ∀ d : Fin D, 2 ^ (e + (d.val + 1)) * (c / m ^ (d.val + 1) % m) =
          2 ^ (e + 1 + d.val) * (c / m / m ^ d.val % m) := by
        intro d
        rw [Nat.div_div_eq_div_mul, ← pow_succ', show e + (d.val + 1) = e + 1 + d.val by omega]
      simp only [hs]
      ring
  have h := key D c.val 0
  simp only [Nat.zero_add] at h
  rw [← h]
  rfl

/-! ## The table, row by row -/

/-- The writer's row of code `c`: its one-hot blocks, then its acceptance bit. -/
def rowOf (m D p res c : ℕ) : List Bool :=
  blocksOf m (digitsOf m D c) ++ [decide ((res + radixList (digitsOf m D c) 0) % p = 0)]

/-- The first `i` rows. -/
def tabPrefix (m D p res : ℕ) : ℕ → List Bool
  | 0 => []
  | i + 1 => tabPrefix m D p res i ++ rowOf m D p res i

theorem rowOf_length (m D p res c : ℕ) : (rowOf m D p res c).length = D * m + 1 := by
  rw [rowOf, List.length_append, blocksOf_length, digitsOf_length, List.length_singleton]

theorem tabPrefix_length (m D p res : ℕ) : ∀ i, (tabPrefix m D p res i).length = i * (D * m + 1) := by
  intro i
  induction i with
  | zero => simp [tabPrefix]
  | succ i ih => rw [tabPrefix, List.length_append, ih, rowOf_length, Nat.succ_mul]

theorem flatten_ofFn_nat {α : Type} (f : ℕ → List α) (pre : ℕ → List α) (h0 : pre 0 = [])
    (hs : ∀ i, pre (i + 1) = pre i ++ f i) : ∀ N, (List.ofFn (fun c : Fin N => f c.val)).flatten = pre N := by
  intro N
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append, hs N]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih]

/-- **The writer's `N = m^D` rows are the consumer's table.** -/
theorem tabPrefix_full (pop D p res : ℕ) :
    thrTable D (pop + 1) ((pop + 1) ^ D) tupleOf
        (fun c => SupplierRadix.modularTupleAccepts p res 2 (tupleOf c)) =
      tabPrefix (pop + 1) D p res ((pop + 1) ^ D) := by
  unfold thrTable
  have hrow : (fun c : Fin ((pop + 1) ^ D) => selBits D (pop + 1) (tupleOf c) ++
      [SupplierRadix.modularTupleAccepts p res 2 (tupleOf c)]) =
      (fun c : Fin ((pop + 1) ^ D) => rowOf (pop + 1) D p res c.val) := by
    funext c
    rw [selBits_tupleOf, rowOf, SupplierRadix.modularTupleAccepts, radixValue_tupleOf]
  rw [hrow]
  exact flatten_ofFn_nat (rowOf (pop + 1) D p res) (tabPrefix (pop + 1) D p res) rfl (fun _ => rfl) _

end NearCubicWires.PacketsCombine

