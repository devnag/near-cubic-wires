import Proof.Rows.RowsKeyTop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymC5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc
open RowsConstruction.BaseLayout RowsConstruction.KeyStep
noncomputable section

/-! ## 1. Generic facts about the carry cascade `next` -/

section Generic
variable {ι : Type} [DecidableEq ι]

theorem zeroS_append : ∀ (ls tl : List (Level ι)) (x : ι → ℕ), zero (ls ++ tl) x = zero tl (zero ls x)
  | [], _, _ => rfl
  | l :: ls, tl, x => by
    simp only [List.cons_append, zero]
    exact zeroS_append ls tl _

/-- If the tail overflows, the cascade over `ls ++ tl` is the cascade over `ls`, with the tail reset. -/
theorem nextS_append_none : ∀ (ls tl : List (Level ι)) (d : ι → ℕ), next tl d = none →
    next (ls ++ tl) d = (next ls d).map (zero tl)
  | [], _, _, h => by simp only [List.nil_append, h]; rfl
  | l :: ls, tl, d, h => by
    rw [List.cons_append]
    have ih := nextS_append_none ls tl d h
    cases hn : next ls d with
    | some e =>
      rw [next_cons_of_some _ _ _ _ (by rw [ih, hn]; rfl), next_cons_of_some _ _ _ _ hn]
      rfl
    | none =>
      rw [next_cons_of_none _ _ _ (by rw [ih, hn]; rfl), next_cons_of_none _ _ _ hn]
      split_ifs
      · simp only [Option.map_some, zeroS_append]
      · rfl

/-- Levels of bound at most `1` never advance. -/
theorem nextS_le_one : ∀ (ls : List (Level ι)) (d : ι → ℕ), (∀ l ∈ ls, ∀ x, l.bound x ≤ 1) → next ls d = none
  | [], _, _ => rfl
  | l :: ls, d, h => by
    rw [next_cons_of_none _ _ _ (nextS_le_one ls d (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')))]
    have := h l List.mem_cons_self d
    rw [if_neg (by omega)]

theorem zeroS_not_mem : ∀ (ls : List (Level ι)) (x : ι → ℕ) (f : ι), (∀ l ∈ ls, l.field ≠ f) → zero ls x f = x f
  | [], _, _, _ => rfl
  | l :: ls, x, f, h => by
    simp only [zero]
    rw [zeroS_not_mem ls _ f (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')),
      Function.update_of_ne (h l List.mem_cons_self).symm]

theorem zeroS_mem : ∀ (ls : List (Level ι)) (x : ι → ℕ) (f : ι), (∃ l ∈ ls, l.field = f) → zero ls x f = 0
  | [], _, _, h => by obtain ⟨l, hl, _⟩ := h; simp at hl
  | l :: ls, x, f, h => by
    simp only [zero]
    by_cases h' : ∃ l' ∈ ls, l'.field = f
    · exact zeroS_mem ls _ f h'
    · simp only [not_exists, not_and] at h'
      rw [zeroS_not_mem ls _ f h']
      obtain ⟨l', hl', he⟩ := h
      rcases List.mem_cons.mp hl' with rfl | hl''
      · rw [← he, Function.update_self]
      · exact absurd he (h' l' hl'')

theorem zeroS_zero : ∀ (ls : List (Level ι)), zero ls (fun _ => 0) = fun _ => 0
  | [] => rfl
  | l :: ls => by
    simp only [zero]
    have e : Function.update (fun _ : ι => (0 : ℕ)) l.field 0 = fun _ => 0 := by
      funext x; by_cases hx : x = l.field <;> simp [hx]
    rw [e]
    exact zeroS_zero ls

end Generic

/-! ## 2. The physical five-level cascade (seed, then offsets 0..3; offset 3 innermost) -/

def o8 (c : Fin 4) : Fin 8 := ⟨c.val, by omega⟩

/-- Offset level `c` with a constant bound. -/
def olv (c : Fin 4) (b : ℕ) : Level (Fin 8) := ⟨o8 c, fun _ => b⟩

/-- The seed level (field 5). -/
def slv (N : ℕ) : Level (Fin 8) := ⟨5, fun _ => N⟩

/-- The five levels, outermost first. -/
def S5 (N : ℕ) (b : Fin 4 → ℕ) : List (Level (Fin 8)) :=
  [slv N, olv 0 (b 0), olv 1 (b 1), olv 2 (b 2), olv 3 (b 3)]

/-- **The physical cascade** on (seed index `e`, padded offsets `o`): advance the innermost digit that can advance,
clear the ones inside it; seed and offsets all `0` when every level overflows (the wrap to key 0). -/
def cascS (N : ℕ) (b : Fin 4 → ℕ) (e : ℕ) (o : Fin 4 → ℕ) : ℕ × (Fin 4 → ℕ) :=
  if o 3 + 1 < b 3 then (e, Function.update o 3 (o 3 + 1))
  else if o 2 + 1 < b 2 then (e, Function.update (Function.update o 3 0) 2 (o 2 + 1))
  else if o 1 + 1 < b 1 then (e, Function.update (Function.update (Function.update o 3 0) 2 0) 1 (o 1 + 1))
  else if o 0 + 1 < b 0 then
    (e, Function.update (Function.update (Function.update (Function.update o 3 0) 2 0) 1 0) 0 (o 0 + 1))
  else if e + 1 < N then
    (e + 1, Function.update (Function.update (Function.update (Function.update o 3 0) 2 0) 1 0) 0 0)
  else (0, Function.update (Function.update (Function.update (Function.update o 3 0) 2 0) 1 0) 0 0)

/-- Read (seed, offsets) off a cascade result; the past-the-end code reads as all `0`. -/
def rdS : Option (Fin 8 → ℕ) → ℕ × (Fin 4 → ℕ)
  | some E => (E 5, fun c => E (o8 c))
  | none => (0, fun _ => 0)

theorem olv_step (c : Fin 4) (b : ℕ) (D : Fin 8 → ℕ) (h : D (o8 c) + 1 < b) :
    next [olv c b] D = some (Function.update D (o8 c) (D (o8 c) + 1)) := by
  rw [next_cons_of_none _ _ _ rfl]
  simp only [olv, zero]
  rw [if_pos h]

theorem olv_none (c : Fin 4) (b : ℕ) (D : Fin 8 → ℕ) (ls : List (Level (Fin 8))) (hls : next ls D = none)
    (h : ¬ D (o8 c) + 1 < b) : next (olv c b :: ls) D = none := by
  rw [next_cons_of_none _ _ _ hls]
  simp only [olv]
  rw [if_neg h]

theorem olv_some (c : Fin 4) (b : ℕ) (D : Fin 8 → ℕ) (ls : List (Level (Fin 8))) (hls : next ls D = none)
    (h : D (o8 c) + 1 < b) :
    next (olv c b :: ls) D = some (zero ls (Function.update D (o8 c) (D (o8 c) + 1))) := by
  rw [next_cons_of_none _ _ _ hls]
  simp only [olv]
  rw [if_pos h]

/-- **The cascade over the five levels is `cascS`.** -/
theorem next_S5 (N : ℕ) (b : Fin 4 → ℕ) (D : Fin 8 → ℕ) :
    rdS (next (S5 N b) D) = cascS N b (D 5) (fun c => D (o8 c)) := by
  unfold S5 cascS
  simp only []
  by_cases h3 : D (o8 3) + 1 < b 3
  · rw [if_pos h3, next_cons_of_some _ _ _ _ (next_cons_of_some _ _ _ _ (next_cons_of_some _ _ _ _
      (next_cons_of_some _ _ _ _ (olv_step 3 (b 3) D h3))))]
    simp only [rdS, Prod.mk.injEq]
    refine ⟨by simp [o8], funext fun c => ?_⟩
    fin_cases c <;> simp [o8]
  have n3 : next [olv 3 (b 3)] D = none := olv_none 3 (b 3) D [] rfl h3
  rw [if_neg h3]
  by_cases h2 : D (o8 2) + 1 < b 2
  · rw [if_pos h2, next_cons_of_some _ _ _ _ (next_cons_of_some _ _ _ _ (next_cons_of_some _ _ _ _
      (olv_some 2 (b 2) D _ n3 h2)))]
    simp only [rdS, Prod.mk.injEq]
    refine ⟨by simp [o8, olv, zero], funext fun c => ?_⟩
    fin_cases c <;> simp [o8, olv, zero]
  have n2 := olv_none 2 (b 2) D _ n3 h2
  rw [if_neg h2]
  by_cases h1 : D (o8 1) + 1 < b 1
  · rw [if_pos h1, next_cons_of_some _ _ _ _ (next_cons_of_some _ _ _ _ (olv_some 1 (b 1) D _ n2 h1))]
    simp only [rdS, Prod.mk.injEq]
    refine ⟨by simp [o8, olv, zero], funext fun c => ?_⟩
    fin_cases c <;> simp [o8, olv, zero]
  have n1 := olv_none 1 (b 1) D _ n2 h1
  rw [if_neg h1]
  by_cases h0 : D (o8 0) + 1 < b 0
  · rw [if_pos h0, next_cons_of_some _ _ _ _ (olv_some 0 (b 0) D _ n1 h0)]
    simp only [rdS, Prod.mk.injEq]
    refine ⟨by simp [o8, olv, zero], funext fun c => ?_⟩
    fin_cases c <;> simp [o8, olv, zero]
  have n0 := olv_none 0 (b 0) D _ n1 h0
  rw [if_neg h0, next_cons_of_none _ _ _ n0]
  by_cases hs : D 5 + 1 < N
  · simp only [slv]
    rw [if_pos hs, if_pos hs]
    simp only [rdS, Prod.mk.injEq]
    refine ⟨by simp [o8, olv, zero], funext fun c => ?_⟩
    fin_cases c <;> simp [o8, olv, zero]
  · simp only [slv]
    rw [if_neg hs, if_neg hs]
    simp only [rdS, Prod.mk.injEq]
    refine ⟨by simp, funext fun c => ?_⟩
    fin_cases c <;> simp

/-! ## 3. The SYM request's cascade is `cascS` on the padded bounds -/

/-- Generic padded bounds: `g c` below `n`, `1` from `n` to `3`. -/
def sbndN (n : ℕ) (g : Fin n → ℕ) (c : Fin 4) : ℕ := if h : c.val < n then g ⟨c.val, h⟩ else 1

/-- Generic radix-1 padding levels `n..3`. -/
def spadsN (n : ℕ) (h : n ≤ 4) : List (Level (Fin 8)) :=
  List.ofFn (fun i : Fin (4 - n) => (⟨⟨n + i.val, by omega⟩, fun _ => 1⟩ : Level (Fin 8)))

theorem coord_pads (n : ℕ) (h : n ≤ 4) (g : Fin n → ℕ) :
    coordLevels 0 n (by omega) g ++ spadsN n h =
      [olv 0 (sbndN n g 0), olv 1 (sbndN n g 1), olv 2 (sbndN n g 2), olv 3 (sbndN n g 3)] := by
  interval_cases n <;> simp [coordLevels, spadsN, olv, o8, sbndN, List.ofFn_succ]

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

abbrev skeys := RCFive.RowKeys.symKeys r L target
abbrev sdig := symDigitsOf r L target
abbrev sspec := cursorSpec a (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target)
/-- The seed count of the SYM family. -/
abbrev sNS : ℕ := (symSeeds r L target).length

/-- The four offset bounds: `bottomCount+1` for the request's circuits, `1` past them (radix-1 padding). -/
def sbnd (c : Fin 4) : ℕ := sbndN r.circuits.length (fun i => (r.circuits.get i).bottomCount + 1) c

/-- A key's offsets, padded by `0` to four slots (the words `RowsBaseLayout.symOffWords` frame). -/
def offN (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) : ℕ :=
  if h : c.val < r.circuits.length then k.offset ⟨c.val, h⟩ else 0

/-- The radix-1 padding levels. -/
def spads : List (Level (Fin 8)) := spadsN r.circuits.length four

theorem spads_le_one : ∀ l ∈ spads r four, ∀ x, l.bound x ≤ 1 := by
  intro l hl x
  simp only [spads, spadsN, List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  simp

theorem sspec_pads : sspec a r four L target ++ spads r four = S5 (sNS r L target) (sbnd r) := by
  have h := coord_pads r.circuits.length four (fun i => (r.circuits.get i).bottomCount + 1)
  simp only [sspec, cursorSpec, spads, List.cons_append]
  rw [h]
  rfl

theorem spads_field_ne5 : ∀ l ∈ spads r four, l.field ≠ 5 := by
  intro l hl e
  simp only [spads, spadsN, List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  have := congrArg Fin.val e
  simp at this
  omega

include four in
theorem spads_fields (c : Fin 4) (hc : ¬ c.val < r.circuits.length) : ∃ l ∈ spads r four, l.field = o8 c := by
  refine ⟨⟨⟨r.circuits.length + (c.val - r.circuits.length), by omega⟩, fun _ => 1⟩, ?_, ?_⟩
  · simp only [spads, spadsN, List.mem_ofFn]
    exact ⟨⟨c.val - r.circuits.length, by omega⟩, rfl⟩
  · simp only [o8]
    apply Fin.ext
    simp only
    omega

theorem spads_not_fields (c : Fin 4) (hc : c.val < r.circuits.length) : ∀ l ∈ spads r four, l.field ≠ o8 c := by
  intro l hl
  simp only [spads, spadsN, List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  intro e
  have := congrArg Fin.val e
  simp [o8] at this
  omega

theorem sdig_off (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) :
    sdig r L target k (o8 c) = offN r L target k c := by
  unfold sdig symDigitsOf offN
  by_cases hc : c.val < r.circuits.length
  · rw [dif_pos (by simpa [o8] using hc), dif_pos hc]
    rfl
  · rw [dif_neg (by simpa [o8] using hc), dif_neg hc]
    have h5 : ¬ (o8 c).val = 5 := by simp [o8]; omega
    rw [if_neg h5]

include four in
theorem sdig_seed (k : RCFive.RowKeys.SymKey r L target) : sdig r L target k 5 = symSeedIdx r L target k := by
  unfold sdig symDigitsOf
  rw [dif_neg (by simp; omega), if_pos (show ((5 : Fin 8) : ℕ) = 5 from rfl)]
  rfl

theorem seedIdx_lt (k : RCFive.RowKeys.SymKey r L target) : symSeedIdx r L target k < sNS r L target := by
  simp only [symSeedIdx, sNS, symSeeds, PCJ9eff70d512234a4c_Fixed.Packets.seedList, List.length_ofFn]
  exact Fin.isLt _

theorem sNS_lt : sNS r L target < 2^(natBitLength (sNS r L target)) :=
  Nat.lt_pow_succ_log_self (by decide) _

theorem keyAt_eq (j : Nat) (hj : j < (skeys r L target).length) :
    symKeyAt r L target j = some (skeys r L target)[j] := by
  simp only [symKeyAt, Nat.mod_eq_of_lt hj, List.getElem?_eq_getElem hj]

theorem skeys_ne (j : Nat) (hj : j < (skeys r L target).length) :
    PacketFamilyParent.rcKeys a (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target) ≠ [] := by
  change skeys r L target ≠ []
  intro h
  rw [h] at hj
  simp at hj

theorem sdigits : (skeys r L target).map (sdig r L target) = enum (sspec a r four L target) (fun _ => 0) :=
  sym_digits a r four L target

/-- Consecutive keys: the carry cascade maps `keys[j]`'s digits to `keys[j+1]`'s. -/
theorem sym_next (j : Nat) (hj : j+1 < (skeys r L target).length) :
    next (sspec a r four L target) (sdig r L target (skeys r L target)[j]) =
      some (sdig r L target (skeys r L target)[j+1]) := by
  have hc := (enum_next (sspec a r four L target) (cursorSpec_wf a _)
    (cursorSpec_pos a _ (skeys_ne a r four L target j (by omega))) (fun _ => 0)).1
  rw [← sdigits a r four L target] at hc
  have h := hc.getElem j (by rw [List.length_map]; exact hj)
  simpa only [List.getElem_map] using h

/-- The last key's digits have no successor. -/
theorem sym_last (j : Nat) (hj : j < (skeys r L target).length) (hl : j+1 = (skeys r L target).length) :
    next (sspec a r four L target) (sdig r L target (skeys r L target)[j]) = none := by
  have hl' := (enum_next (sspec a r four L target) (cursorSpec_wf a _)
    (cursorSpec_pos a _ (skeys_ne a r four L target j hj)) (fun _ => 0)).2.1
  rw [← sdigits a r four L target] at hl'
  apply hl'
  have e : (skeys r L target).length - 1 = j := by omega
  rw [List.getLast?_eq_getElem?, List.length_map, e, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

include a four in

theorem sym_key0 (h0 : 0 < (skeys r L target).length) :
    sdig r L target (skeys r L target)[0] = fun _ => 0 := by
  have hh := (enum_next (sspec a r four L target) (cursorSpec_wf a _)
    (cursorSpec_pos a _ (skeys_ne a r four L target 0 h0)) (fun _ => 0)).2.2
  rw [← sdigits a r four L target, zeroS_zero, List.head?_map, List.head?_eq_getElem?,
    List.getElem?_eq_getElem h0] at hh
  exact Option.some.inj hh

include a four in
/-- **The key of row `j+1`** (on the last row: key 0) is the physical cascade of row `j`'s (seed, offsets). -/
theorem sym_succ (j : Nat) (hj : j < (skeys r L target).length) :
    ∃ k' : RCFive.RowKeys.SymKey r L target, symKeyAt r L target (j+1) = some k' ∧ k' ∈ skeys r L target ∧
      (symSeedIdx r L target k', offN r L target k') =
        cascS (sNS r L target) (sbnd r) (symSeedIdx r L target (skeys r L target)[j])
          (offN r L target (skeys r L target)[j]) := by
  set D := sdig r L target (skeys r L target)[j] with hD
  have hS5 := next_S5 (sNS r L target) (sbnd r) D
  have e5 : D 5 = symSeedIdx r L target (skeys r L target)[j] := by rw [hD, sdig_seed r four]
  have eo : (fun c => D (o8 c)) = offN r L target (skeys r L target)[j] := by
    funext c; rw [hD, sdig_off r]
  rw [e5, eo, ← sspec_pads a r four L target,
    nextS_append_none _ _ D (nextS_le_one _ D (spads_le_one r four))] at hS5
  rw [← hS5]
  by_cases hj1 : j+1 < (skeys r L target).length
  · refine ⟨(skeys r L target)[j+1], keyAt_eq r L target (j+1) hj1, List.getElem_mem hj1, ?_⟩
    rw [sym_next a r four L target j hj1]
    simp only [Option.map_some, rdS, Prod.mk.injEq]
    refine ⟨?_, funext fun c => ?_⟩
    · rw [zeroS_not_mem _ _ 5 (spads_field_ne5 r four), sdig_seed r four]
    · by_cases hc : c.val < r.circuits.length
      · rw [zeroS_not_mem _ _ _ (spads_not_fields r four c hc), sdig_off r]
      · rw [zeroS_mem _ _ _ (spads_fields r four c hc)]
        simp [offN, hc]
  · have hl : j+1 = (skeys r L target).length := by omega
    have h0 : 0 < (skeys r L target).length := by omega
    refine ⟨(skeys r L target)[0], ?_, List.getElem_mem h0, ?_⟩
    · simp only [symKeyAt]
      rw [hl, Nat.mod_self, List.getElem?_eq_getElem h0]
    · rw [sym_last a r four L target j hj hl]
      simp only [Option.map_none, rdS, Prod.mk.injEq]
      have hz := sym_key0 a r four L target h0
      refine ⟨?_, funext fun c => ?_⟩
      · rw [← sdig_seed r four, hz]
      · rw [← sdig_off r, hz]

end Sym

/-! ## 4. The cumulative targets as a function of the padded offsets -/

/-- The four cumulative targets of padded offsets `o` for `n` circuits (`0` past the circuits). -/
def tgv (n : ℕ) (o : Fin 4 → ℕ) : Fin 4 → ℕ :=
  ![if 0 < n then o 0 else 0, if 1 < n then o 0 + o 1 + 1 else 0,
    if 2 < n then o 0 + o 1 + o 2 + 2 else 0, if 3 < n then o 0 + o 1 + o 2 + o 3 + 3 else 0]

theorem tgv_ge (n : ℕ) (o : Fin 4 → ℕ) (c : Fin 4) (hc : ¬ c.val < n) : tgv n o c = 0 := by
  fin_cases c <;> simp_all [tgv]

theorem tgv_zero (n : ℕ) (o : Fin 4 → ℕ) (h : 0 < n) : tgv n o 0 = o 0 + 0 := by
  simp [tgv, h]

theorem tgv_succ (n : ℕ) (o : Fin 4 → ℕ) (c : Fin 4) (h0 : 0 < c.val) (hc : c.val < n) :
    tgv n o c = tgv n o ⟨c.val - 1, by omega⟩ + o c + 1 := by
  fin_cases c
  · simp at h0
  all_goals (simp at hc; simp [tgv]; split_ifs <;> omega)

section Sym
variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : Nat)

include four in
/-- **The resident target of slot `c` is `tgv` of the padded offsets.** -/
theorem tg_eq (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) :
    SymVerdict.Tg r k.offset c = tgv r.circuits.length (offN r L target k) c := by
  have hN : ∀ i : ℕ, SymMeaning.offsetN r k.offset i =
      if h : i < r.circuits.length then k.offset ⟨i, h⟩ else 0 := fun i => rfl
  unfold SymVerdict.Tg SymMeaning.targetCount
  fin_cases c <;>
    simp [tgv, offN, hN, Finset.sum_range_succ] <;> split_ifs <;> omega

end Sym

/-! ## 5. The SYM master bank: two keys differ exactly at the target ports 140–143 -/

/-- Target port of slot `c` (`SymVerdict.auxP (tIdx c)`). -/
def tgtP (c : Fin 4) : Fin 254 := ⟨140 + c.val, by omega⟩

theorem tgtP_eq (c : Fin 4) : tgtP c = SymVerdict.auxP (SymVerdict.tIdx c) := by
  apply Fin.ext
  rw [SymVerdict.auxP_val]
  simp [tgtP, SymVerdict.tIdx]
  omega

theorem tgtP_ne109 (c : Fin 4) : tgtP c ≠ 109 := by
  intro h
  have := congrArg Fin.val h
  simp [tgtP] at this
  omega

theorem layout_update {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) (j : Fin 18) (v : α) :
    SymVerdict.symLayout F (Function.update A j v) b o =
      Function.update (SymVerdict.symLayout F A b o) (SymVerdict.auxP j) v := by
  unfold SymVerdict.symLayout SymVerdict.auxP
  rw [RowsConstruction.CellInput.addCases_update_left, RowsConstruction.CellInput.addCases_update_right]

theorem auxIn_update (w Dc cap : Nat) (N T T' : Fin 4 → Nat) :
    SymVerdict.auxIn w Dc cap N T' =
      Function.update (Function.update (Function.update (Function.update (SymVerdict.auxIn w Dc cap N T)
        (SymVerdict.tIdx 0) (fb w (T' 0))) (SymVerdict.tIdx 1) (fb w (T' 1))) (SymVerdict.tIdx 2) (fb w (T' 2)))
        (SymVerdict.tIdx 3) (fb w (T' 3)) := by
  funext j
  fin_cases j <;> simp [SymVerdict.auxIn, SymVerdict.tIdx, fb]

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The SYM counter width `T+3`. -/
abbrev sw : Nat := symT a r four L target + 3

/-- The four target updates of a master bank. -/
def tupd (M : Fin 254 → List Bool) (w : Nat) (t : Fin 4 → Nat) : Fin 254 → List Bool :=
  Function.update (Function.update (Function.update (Function.update M (tgtP 0) (fb w (t 0))) (tgtP 1) (fb w (t 1)))
    (tgtP 2) (fb w (t 2))) (tgtP 3) (fb w (t 3))

theorem tgtP_key (c : Fin 4) : tgtP c ∈ symKeySet := by
  fin_cases c <;> decide

/-- Key ports keep their word under `keyPad`, so padding commutes with the target updates. -/
theorem keyPad_tupd (R : Nat) (X : Fin 254 → List Bool) (w : Nat) (t : Fin 4 → Nat) :
    (fun i => keyPad symKeySet R i (tupd X w t i)) = tupd (fun i => keyPad symKeySet R i (X i)) w t := by
  funext i
  unfold tupd
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | (subst_vars; exact keyPad_key R (tgtP_key _) _)

theorem input_update (I : Finset (Fin r.q)) (x : BitInput r.q) (T w Dc cap : Nat)
    (o o' : Fin r.circuits.length → Nat) :
    SymVerdict.input r I x L target T w Dc cap o' =
      tupd (SymVerdict.input r I x L target T w Dc cap o) w (fun c => SymVerdict.Tg r o' c) := by
  unfold tupd SymVerdict.input
  rw [auxIn_update w Dc cap (SymVerdict.N r) (SymVerdict.Tg r o) (SymVerdict.Tg r o'), layout_update, layout_update,
    layout_update, layout_update, tgtP_eq, tgtP_eq, tgtP_eq, tgtP_eq]

theorem masters_upd (R : Nat) (k k' : RCFive.RowKeys.SymKey r L target) :
    symMasters a r four L target R k' =
      tupd (symMasters a r four L target R k) (sw a r four L target) (fun c => SymVerdict.Tg r k'.offset c) := by
  have hM : ∀ kk : RCFive.RowKeys.SymKey r L target, symMasters a r four L target R kk =
      Function.update (fun i => keyPad symKeySet R i (SymVerdict.input r (symLive r L) (fun _ => false) L target
        (symT a r four L target) (symT a r four L target+3) (2*(symT a r four L target+3)+1)
        (symCap r.q (symT a r four L target)) kk.offset i)) 109 (List.replicate R false) := by
    intro kk
    funext i
    simp only [symMasters, Function.update_apply]
  rw [hM, hM, input_update r L target _ _ _ _ _ _ k.offset k'.offset, keyPad_tupd]
  unfold tupd
  rw [Function.update_comm (tgtP_ne109 3), Function.update_comm (tgtP_ne109 2), Function.update_comm (tgtP_ne109 1),
    Function.update_comm (tgtP_ne109 0)]

/-- The master at a target port. -/
theorem masters_tgt (R : Nat) (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) :
    symMasters a r four L target R k (tgtP c) = fb (sw a r four L target) (SymVerdict.Tg r k.offset c) := by
  simp only [symMasters, if_neg (tgtP_ne109 c)]
  rw [keyPad_key R (tgtP_key c), tgtP_eq]
  unfold SymVerdict.input
  rw [SymVerdict.layout_aux]
  fin_cases c <;> rfl

/-! ## 6. Numeric side conditions -/

theorem bottom_le (c : Fin 4) (hc : c.val < r.circuits.length) :
    (r.circuits.get ⟨c.val, hc⟩).bottomCount ≤ symT a r four L target + 1 := by
  have hN := sym_N_le a r four L target c
  unfold SymVerdict.N SymMeaning.driverLen at hN
  rw [if_pos hc] at hN
  have hg : SymMeaning.gateCount r c.val = (r.circuits.get ⟨c.val, hc⟩).bottomCount := by
    simp [SymMeaning.gateCount, SymMeaning.symGates, List.getD_eq_getElem?_getD, hc]
  omega

theorem sbnd_lt (c : Fin 4) : sbnd r c < 2^(sw a r four L target) := by
  have h : sbnd r c ≤ symT a r four L target + 2 := by
    unfold sbnd sbndN
    split
    · have := bottom_le a r four L target c (by assumption)
      simp only [List.get_eq_getElem] at this ⊢
      omega
    · omega
  have h2 : symT a r four L target + 2 < 2^(symT a r four L target + 3) := by
    have := Nat.lt_two_pow_self (n := symT a r four L target + 3)
    omega
  exact lt_of_le_of_lt h h2

theorem offN_lt (k : RCFive.RowKeys.SymKey r L target) (hk : k ∈ skeys r L target) (c : Fin 4) :
    offN r L target k c < sbnd r c := by
  unfold offN sbnd sbndN
  by_cases hc : c.val < r.circuits.length
  · rw [dif_pos hc, dif_pos hc]
    have := sym_offset_le r L target k hk ⟨c.val, hc⟩
    simp only [SymMeaning.symGates, List.length_ofFn] at this
    dsimp only
    omega
  · rw [dif_neg hc, dif_neg hc]
    omega

theorem tg_lt (k : RCFive.RowKeys.SymKey r L target) (hk : k ∈ skeys r L target) (c : Fin 4) :
    SymVerdict.Tg r k.offset c < 2^(sw a r four L target) :=
  (sym_spec a r four L target k.offset (sym_offset_le r L target k hk)).2.2.2.1 c

theorem sw_fits (k : RCFive.RowKeys.SymKey r L target) :
    2 * sw a r four L target + 1 ≤ symRes r.q (symT a r four L target) := by
  have h := sym_hml a r four L target (symRes r.q (symT a r four L target)) (symR_le_res _ _) k (tgtP 0)
  rw [masters_tgt, fb, frame_length, SignedSortKey.binary_length] at h
  exact h

end Sym

end
end RowsConstruction.SymC5
