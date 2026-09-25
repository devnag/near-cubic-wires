import Proof.Rows.RowsThrKey

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrSel
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeySucc RowsConstruction.KeyTop
open RowsConstruction.ThrKey
noncomputable section

/-! ## 1. Generic facts about the carry cascade `next` -/

section Generic
variable {ι : Type} [DecidableEq ι]

theorem zero_append : ∀ (ls tl : List (Level ι)) (x : ι → ℕ), zero (ls ++ tl) x = zero tl (zero ls x)
  | [], _, _ => rfl
  | l :: ls, tl, x => by
    simp only [List.cons_append, zero]
    exact zero_append ls tl _

/-- If the tail overflows, the cascade over `ls ++ tl` is the cascade over `ls`, with the tail reset. -/
theorem next_append_none : ∀ (ls tl : List (Level ι)) (d : ι → ℕ), next tl d = none →
    next (ls ++ tl) d = (next ls d).map (zero tl)
  | [], _, _, h => by simp only [List.nil_append, h]; rfl
  | l :: ls, tl, d, h => by
    rw [List.cons_append]
    have ih := next_append_none ls tl d h
    cases hn : next ls d with
    | some e =>
      rw [next_cons_of_some _ _ _ _ (by rw [ih, hn]; rfl), next_cons_of_some _ _ _ _ hn]
      rfl
    | none =>
      rw [next_cons_of_none _ _ _ (by rw [ih, hn]; rfl), next_cons_of_none _ _ _ hn]
      split_ifs
      · simp only [Option.map_some, zero_append]
      · rfl

/-- Levels of bound at most `1` never advance. -/
theorem next_le_one : ∀ (ls : List (Level ι)) (d : ι → ℕ), (∀ l ∈ ls, ∀ x, l.bound x ≤ 1) → next ls d = none
  | [], _, _ => rfl
  | l :: ls, d, h => by
    rw [next_cons_of_none _ _ _ (next_le_one ls d (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')))]
    have := h l List.mem_cons_self d
    rw [if_neg (by omega)]

theorem zero_not_mem : ∀ (ls : List (Level ι)) (x : ι → ℕ) (f : ι), (∀ l ∈ ls, l.field ≠ f) → zero ls x f = x f
  | [], _, _, _ => rfl
  | l :: ls, x, f, h => by
    simp only [zero]
    rw [zero_not_mem ls _ f (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')),
      Function.update_of_ne (h l List.mem_cons_self).symm]

theorem zero_mem : ∀ (ls : List (Level ι)) (x : ι → ℕ) (f : ι), (∃ l ∈ ls, l.field = f) → zero ls x f = 0
  | [], _, _, h => by obtain ⟨l, hl, _⟩ := h; simp at hl
  | l :: ls, x, f, h => by
    simp only [zero]
    by_cases h' : ∃ l' ∈ ls, l'.field = f
    · exact zero_mem ls _ f h'
    · simp only [not_exists, not_and] at h'
      rw [zero_not_mem ls _ f h']
      obtain ⟨l', hl', he⟩ := h
      rcases List.mem_cons.mp hl' with rfl | hl''
      · rw [← he, Function.update_self]
      · exact absurd he (h' l' hl'')

theorem zero_zero : ∀ (ls : List (Level ι)), zero ls (fun _ => 0) = fun _ => 0
  | [] => rfl
  | l :: ls => by
    simp only [zero]
    have e : Function.update (fun _ : ι => (0 : ℕ)) l.field 0 = fun _ => 0 := by
      funext x; by_cases hx : x = l.field <;> simp [hx]
    rw [e]
    exact zero_zero ls

end Generic

/-! ## 2. The physical four-digit cascade -/

def c4 (c : Fin 4) : Fin 8 := ⟨c.val, by omega⟩

/-- Level `c` with a constant bound. -/
def lv (c : Fin 4) (b : ℕ) : Level (Fin 8) := ⟨c4 c, fun _ => b⟩

/-- The four child-digit levels, outermost first. -/
def P4 (b : Fin 4 → ℕ) : List (Level (Fin 8)) := [lv 0 (b 0), lv 1 (b 1), lv 2 (b 2), lv 3 (b 3)]

/-- **The physical cascade**: advance the innermost digit that can advance, clear the ones inside it; all zero when
every digit overflows (the wrap). -/
def casc (b d : Fin 4 → ℕ) : Fin 4 → ℕ :=
  if d 3 + 1 < b 3 then Function.update d 3 (d 3 + 1)
  else if d 2 + 1 < b 2 then Function.update (Function.update d 3 0) 2 (d 2 + 1)
  else if d 1 + 1 < b 1 then Function.update (Function.update (Function.update d 3 0) 2 0) 1 (d 1 + 1)
  else if d 0 + 1 < b 0 then
    Function.update (Function.update (Function.update (Function.update d 3 0) 2 0) 1 0) 0 (d 0 + 1)
  else fun _ => 0

/-- Read the child digits of a cascade result (`0` past the end). -/
def rd (o : Option (Fin 8 → ℕ)) (c : Fin 4) : ℕ :=
  match o with
  | some E => E (c4 c)
  | none => 0

theorem lv_step (c : Fin 4) (b : ℕ) (D : Fin 8 → ℕ) (h : D (c4 c) + 1 < b) :
    next [lv c b] D = some (Function.update D (c4 c) (D (c4 c) + 1)) := by
  rw [next_cons_of_none _ _ _ rfl]
  simp only [lv, zero]
  rw [if_pos h]

theorem lv_none (c : Fin 4) (b : ℕ) (D : Fin 8 → ℕ) (ls : List (Level (Fin 8))) (hls : next ls D = none)
    (h : ¬ D (c4 c) + 1 < b) : next (lv c b :: ls) D = none := by
  rw [next_cons_of_none _ _ _ hls]
  simp only [lv]
  rw [if_neg h]

theorem lv_some (c : Fin 4) (b : ℕ) (D : Fin 8 → ℕ) (ls : List (Level (Fin 8))) (hls : next ls D = none)
    (h : D (c4 c) + 1 < b) :
    next (lv c b :: ls) D = some (zero ls (Function.update D (c4 c) (D (c4 c) + 1))) := by
  rw [next_cons_of_none _ _ _ hls]
  simp only [lv]
  rw [if_pos h]

/-- **The cascade over the four levels is `casc`.** -/
theorem next_P4 (b : Fin 4 → ℕ) (D : Fin 8 → ℕ) :
    rd (next (P4 b) D) = casc b (fun c => D (c4 c)) := by
  unfold P4 casc
  by_cases h3 : D (c4 3) + 1 < b 3
  · rw [if_pos h3, next_cons_of_some _ _ _ _ (next_cons_of_some _ _ _ _ (next_cons_of_some _ _ _ _
      (lv_step 3 (b 3) D h3)))]
    funext c
    fin_cases c <;> simp [rd, c4]
  have n3 : next [lv 3 (b 3)] D = none := lv_none 3 (b 3) D [] rfl h3
  rw [if_neg h3]
  by_cases h2 : D (c4 2) + 1 < b 2
  · rw [if_pos h2, next_cons_of_some _ _ _ _ (next_cons_of_some _ _ _ _ (lv_some 2 (b 2) D _ n3 h2))]
    funext c
    fin_cases c <;> simp [rd, c4, lv, zero]
  have n2 := lv_none 2 (b 2) D _ n3 h2
  rw [if_neg h2]
  by_cases h1 : D (c4 1) + 1 < b 1
  · rw [if_pos h1, next_cons_of_some _ _ _ _ (lv_some 1 (b 1) D _ n2 h1)]
    funext c
    fin_cases c <;> simp [rd, c4, lv, zero]
  have n1 := lv_none 1 (b 1) D _ n2 h1
  rw [if_neg h1]
  by_cases h0 : D (c4 0) + 1 < b 0
  · rw [if_pos h0, lv_some 0 (b 0) D _ n1 h0]
    funext c
    fin_cases c <;> simp [rd, c4, lv, zero]
  · rw [if_neg h0, lv_none 0 (b 0) D _ n1 h0]
    rfl

/-- Generic padded bounds: `g c` below `n`, `1` from `n` to `3`. -/
def bndN (n : ℕ) (g : Fin n → ℕ) (c : Fin 4) : ℕ := if h : c.val < n then g ⟨c.val, h⟩ else 1

/-- Generic radix-1 padding levels `n..3`. -/
def padsN (n : ℕ) (h : n ≤ 4) : List (Level (Fin 8)) :=
  List.ofFn (fun i : Fin (4 - n) => (⟨⟨n + i.val, by omega⟩, fun _ => 1⟩ : Level (Fin 8)))

theorem coordLevels_pads (n : ℕ) (h : n ≤ 4) (g : Fin n → ℕ) :
    coordLevels 0 n (by omega) g ++ padsN n h = P4 (bndN n g) := by
  interval_cases n <;> simp [coordLevels, padsN, P4, lv, c4, bndN, List.ofFn_succ]

/-! ## 3. The THR request's cascade is `casc` on the padded bounds -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The four digit bounds: `|children c|` for the request's circuits, `1` past them (radix-1 padding). -/
def bnd (c : Fin 4) : ℕ :=
  bndN r.circuits.length (fun i => (ThresholdRows.children a (r.circuits.get i)).length) c

/-- The radix-1 padding levels. -/
def pads : List (Level (Fin 8)) := padsN r.circuits.length four

theorem pads_le_one : ∀ l ∈ pads r four, ∀ x, l.bound x ≤ 1 := by
  intro l hl x
  simp only [pads, padsN, List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  simp

theorem coords_pads : coords a r four ++ pads r four = P4 (bnd a r) :=
  coordLevels_pads r.circuits.length four _

include four in
theorem pads_fields (c : Fin 4) (hc : ¬ c.val < r.circuits.length) : ∃ l ∈ pads r four, l.field = c4 c := by
  refine ⟨⟨⟨r.circuits.length + (c.val - r.circuits.length), by omega⟩, fun _ => 1⟩, ?_, ?_⟩
  · simp only [pads, padsN, List.mem_ofFn]
    exact ⟨⟨c.val - r.circuits.length, by omega⟩, rfl⟩
  · simp only [c4]
    apply Fin.ext
    simp only
    omega

theorem pads_not_fields (c : Fin 4) (hc : c.val < r.circuits.length) : ∀ l ∈ pads r four, l.field ≠ c4 c := by
  intro l hl
  simp only [pads, padsN, List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  intro e
  have := congrArg Fin.val e
  simp [c4] at this
  omega

theorem psr_not_fields (c : Fin 4) :
    ∀ l ∈ [Pl a r target, Sl a r L target, Rl a r target], l.field ≠ c4 c := by
  intro l hl e
  have hv := congrArg Fin.val e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  have := c.isLt
  rcases hl with rfl | rfl | rfl <;> simp [Pl, Sl, Rl, c4] at hv <;> omega

/-- Child digits past the request's circuits are `0` in every key. -/
theorem dig_pad (k : RCFive.RowKeys.ThrKey a r L target) (c : Fin 4) (hc : ¬ c.val < r.circuits.length) :
    dig a r L target k (c4 c) = 0 := by
  unfold dig thrDigitsOf
  rw [dif_neg (by simpa [c4] using hc)]
  have := c.isLt
  have h4 : ¬ (c4 c).val = 4 := by simp [c4]; omega
  have h5 : ¬ (c4 c).val = 5 := by simp [c4]; omega
  have h6 : ¬ (c4 c).val = 6 := by simp [c4]; omega
  rw [if_neg h4, if_neg h5, if_neg h6]

include four in
/-- Every key's child digits are below the padded bounds. -/
theorem dig_lt_bnd (k : RCFive.RowKeys.ThrKey a r L target) (c : Fin 4) :
    dig a r L target k (c4 c) < bnd a r c := by
  by_cases hc : c.val < r.circuits.length
  · have e := dig_sel a r four L target k ⟨c.val, hc⟩
    simp only [bnd, bndN, dif_pos hc]
    rw [show c4 c = ⟨c.val, by omega⟩ from rfl, e]
    exact (k.selection ⟨c.val, hc⟩).isLt
  · rw [dig_pad a r L target k c hc]
    simp [bnd, bndN, hc]

include four in
/-- The key's child digits are the base worker's digits. -/
theorem data_digits (k : RCFive.RowKeys.ThrKey a r L target) (c : Fin 4) :
    (PCJ45bee56da9f34d5a_StreamPair.data a r four k.selection).digits c = dig a r L target k (c4 c) := by
  by_cases hc : c.val < r.circuits.length
  · have e := dig_sel a r four L target k ⟨c.val, hc⟩
    rw [show c4 c = ⟨c.val, by omega⟩ from rfl, e]
    simp [PCJ45bee56da9f34d5a_FourfoldBaseData.Data.digits, PCJ45bee56da9f34d5a_StreamPair.data,
      PCJ45bee56da9f34d5a_ThresholdData.data, hc]
  · rw [dig_pad a r L target k c hc]
    simp [PCJ45bee56da9f34d5a_FourfoldBaseData.Data.digits, PCJ45bee56da9f34d5a_StreamPair.data,
      PCJ45bee56da9f34d5a_ThresholdData.data, hc]

/-- The tail (prime, seed, residue) overflows in case Sel. -/
theorem psr_none (d : Fin 8 → ℕ) (hb : ¬ d 6 + 1 < primeAt (cut a r target) (d 4))
    (hs : ¬ d 5 + 1 < (thrSeeds a r L target).length)
    (hp : ¬ d 4 + 1 < NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target)) :
    next [Pl a r target, Sl a r L target, Rl a r target] d = none := by
  have hR : next [Rl a r target] d = none := by
    rw [next_cons_of_none _ _ _ rfl]
    simp only [Rl]
    rw [if_neg hb]
  have hS : next [Sl a r L target, Rl a r target] d = none := by
    rw [next_cons_of_none _ _ _ hR]
    simp only [Sl]
    rw [if_neg hs]
  rw [next_cons_of_none _ _ _ hS]
  simp only [Pl]
  rw [if_neg (by rw [NearCubicWires.PacketsGlue.RequestMeta.card_primeIndex]; exact hp)]

include four in

theorem dig_key0 (h0 : 0 < (KeySucc.keys a r L target).length) :
    dig a r L target (KeySucc.keys a r L target)[0] = fun _ => 0 := by
  have hne : PacketFamilyParent.rcKeys a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target) ≠ [] := by
    change KeySucc.keys a r L target ≠ []
    intro h
    rw [h] at h0
    simp at h0
  have hh := (enum_next (spec a r four L target) (cursorSpec_wf a _) (cursorSpec_pos a _ hne) (fun _ => 0)).2.2
  rw [← thr_digits a r four L target, zero_zero, List.head?_map, List.head?_eq_getElem?,
    List.getElem?_eq_getElem h0] at hh
  exact Option.some.inj hh

include four in
/-- **The key of row `j+1` in case Sel** (on the last row: key 0). Its child digits are the physical cascade of
row `j`'s, and its prime index, seed and residue digits are `0`. -/
theorem sel_key (j : Nat) (hj : j < (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val)
    (h2 : ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length)
    (h3 : ¬ dig a r L target (KeySucc.keys a r L target)[j] 4 + 1 <
      NearCubicWires.PacketsGlue.PrimeCount.pc (cut a r target)) :
    ∃ k' : RCFive.RowKeys.ThrKey a r L target, thrKeyAt a r L target (j+1) = some k' ∧
      (fun c => dig a r L target k' (c4 c)) =
        casc (bnd a r) (fun c => dig a r L target (KeySucc.keys a r L target)[j] (c4 c)) ∧
      dig a r L target k' 4 = 0 ∧ dig a r L target k' 5 = 0 ∧ dig a r L target k' 6 = 0 := by
  set D := dig a r L target (KeySucc.keys a r L target)[j] with hD
  have hpsr := psr_none a r L target D (by rw [hD, dig_res a r four, primeAt_dig a r four]; exact h1)
    (by rw [hD, dig_seed a r four]; exact h2) h3
  have hpads := next_append_none (coords a r four) (pads r four) D (next_le_one _ D (pads_le_one r four))
  rw [coords_pads a r four] at hpads
  by_cases hj1 : j+1 < (KeySucc.keys a r L target).length
  · have hn := thr_next a r four L target j hj1
    rw [spec_eq, next_append_none _ _ D hpsr] at hn
    obtain ⟨e, he, hze⟩ : ∃ e, next (coords a r four) D = some e ∧
        zero [Pl a r target, Sl a r L target, Rl a r target] e = dig a r L target (KeySucc.keys a r L target)[j+1] := by
      cases h : next (coords a r four) D with
      | none => rw [h] at hn; exact absurd hn (by simp)
      | some e => rw [h] at hn; exact ⟨e, rfl, Option.some.inj hn⟩
    refine ⟨(KeySucc.keys a r L target)[j+1], keyAt_eq a r L target (j+1) hj1, ?_, ?_, ?_, ?_⟩
    · rw [← next_P4, hpads, he]
      funext c
      simp only [Option.map_some, rd]
      by_cases hc : c.val < r.circuits.length
      · rw [zero_not_mem _ e _ (pads_not_fields r four c hc), ← hze,
          zero_not_mem _ e _ (psr_not_fields a r L target c)]
      · rw [zero_mem _ e _ (pads_fields r four c hc), dig_pad a r L target _ c hc]
    · rw [← hze]
      exact zero_mem _ e _ ⟨Pl a r target, by simp, rfl⟩
    · rw [← hze]
      exact zero_mem _ e _ ⟨Sl a r L target, by simp, rfl⟩
    · rw [← hze]
      exact zero_mem _ e _ ⟨Rl a r target, by simp, rfl⟩
  · have hl : j+1 = (KeySucc.keys a r L target).length := by omega
    have hn := last_none a r four L target j hj hl
    rw [spec_eq, next_append_none _ _ D hpsr] at hn
    have hc : next (coords a r four) D = none := by
      cases h : next (coords a r four) D with
      | none => rfl
      | some e => rw [h] at hn; exact absurd hn (by simp)
    have h0 : 0 < (KeySucc.keys a r L target).length := by omega
    have hk0 := dig_key0 a r four L target h0
    refine ⟨(KeySucc.keys a r L target)[0], ?_, ?_, by rw [hk0], by rw [hk0], by rw [hk0]⟩
    · simp only [thrKeyAt]
      rw [show (j+1) % (RCFive.RowKeys.thrKeys a r L target).length = 0 from by
        rw [show (RCFive.RowKeys.thrKeys a r L target).length = (KeySucc.keys a r L target).length from rfl, hl,
          Nat.mod_self]]
      exact List.getElem?_eq_getElem h0
    · rw [← next_P4, hpads, hc, hk0]
      rfl

/-! ## 4. The masters of any two keys -/

/-- **Masters of any two keys differ only at the ten key ports.** -/
theorem masters_any (R : Nat) (k k' : RCFive.RowKeys.ThrKey a r L target) :
    thrMasters a r four L target R k' =
      Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (thrMasters a r four L target R k) 242 (fb (wT a r four L target) k'.residue.val))
        240 (fb (wT a r four L target) k'.prime.val)) 149 (fb (wT a r four L target) k'.prime.val))
        218 (fb (wT a r four L target) k'.prime.val))
        209 (ZeroPadding.pad (FT a r four L target) (fb (wT a r four L target) k'.prime.val)))
        228 (fb (RowsConstruction.ThrWidth.T a r four L target)
          ((PCJ45bee56da9f34d5a_StreamPair.data a r four k'.selection).digits 0)))
        229 (fb (RowsConstruction.ThrWidth.T a r four L target)
          ((PCJ45bee56da9f34d5a_StreamPair.data a r four k'.selection).digits 1)))
        230 (fb (RowsConstruction.ThrWidth.T a r four L target)
          ((PCJ45bee56da9f34d5a_StreamPair.data a r four k'.selection).digits 2)))
        231 (fb (RowsConstruction.ThrWidth.T a r four L target)
          ((PCJ45bee56da9f34d5a_StreamPair.data a r four k'.selection).digits 3)))
        220 (ZeroPadding.pad (Uf r.q (RowsConstruction.ThrWidth.T a r four L target))
          (fb (wT a r four L target) (PCJ45bee56da9f34d5a_StreamPair.radix a r four k'.selection))) := by
  funext i
  by_cases h220 : i = 220
  · subst h220
    rw [Function.update_self, masters_at a r four L target R k' 220 (by decide), keyPad_key _ (by decide)]
    exact thr_220 a r four _ _ L target _ _ _ _ _ _ _ _
  rw [Function.update_of_ne h220]
  by_cases h231 : i = 231
  · subst h231
    rw [Function.update_self, masters_at a r four L target R k' 231 (by decide), keyPad_key _ (by decide)]
    exact thr_digit_ports a r four _ _ L target _ _ _ _ _ _ _ _ 3
  rw [Function.update_of_ne h231]
  by_cases h230 : i = 230
  · subst h230
    rw [Function.update_self, masters_at a r four L target R k' 230 (by decide), keyPad_key _ (by decide)]
    exact thr_digit_ports a r four _ _ L target _ _ _ _ _ _ _ _ 2
  rw [Function.update_of_ne h230]
  by_cases h229 : i = 229
  · subst h229
    rw [Function.update_self, masters_at a r four L target R k' 229 (by decide), keyPad_key _ (by decide)]
    exact thr_digit_ports a r four _ _ L target _ _ _ _ _ _ _ _ 1
  rw [Function.update_of_ne h229]
  by_cases h228 : i = 228
  · subst h228
    rw [Function.update_self, masters_at a r four L target R k' 228 (by decide), keyPad_key _ (by decide)]
    exact thr_digit_ports a r four _ _ L target _ _ _ _ _ _ _ _ 0
  rw [Function.update_of_ne h228]
  by_cases h209 : i = 209
  · subst h209
    rw [Function.update_self, masters_at a r four L target R k' 209 (by decide), keyPad_key _ (by decide)]
    exact thr_209 a r four _ _ L target _ _ _ _ _ _ _ _
  rw [Function.update_of_ne h209]
  by_cases h218 : i = 218
  · subst h218
    rw [Function.update_self, masters_at a r four L target R k' 218 (by decide), keyPad_key _ (by decide)]
    exact thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 218 (Or.inr (Or.inl rfl))
  rw [Function.update_of_ne h218]
  by_cases h149 : i = 149
  · subst h149
    rw [Function.update_self, masters_at a r four L target R k' 149 (by decide), keyPad_key _ (by decide)]
    exact thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 149 (Or.inl rfl)
  rw [Function.update_of_ne h149]
  by_cases h240 : i = 240
  · subst h240
    rw [Function.update_self]
    exact masters_240 a r four L target R k'
  rw [Function.update_of_ne h240]
  by_cases h242 : i = 242
  · subst h242
    rw [Function.update_self]
    exact masters_242 a r four L target R k'
  rw [Function.update_of_ne h242]
  by_cases h109 : i = 109
  · subst h109
    rw [thr_hm109, thr_hm109]
  rw [masters_at a r four L target R k' i h109, masters_at a r four L target R k i h109]
  refine congrArg (keyPad thrKeySet R i) (thr_other a r four _ _ L target _ _ _ _ _ _ _ _ _ _ _ _ i ?_)
  simp only [thrKeyPorts, Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ## 5. Case Sel at the bank -/

variable (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-- The bank with the four child-digit masters set to `fb w (e c)`. -/
def digBank (A : Fin (2+rowsWork NI) → List Bool) (w : Nat) (e : Fin 4 → ℕ) : Fin (2+rowsWork NI) → List Bool :=
  Function.update (Function.update (Function.update (Function.update A (masterPort NI 228) (fb w (e 0)))
    (masterPort NI 229) (fb w (e 1))) (masterPort NI 230) (fb w (e 2))) (masterPort NI 231) (fb w (e 3))

include four in

theorem base_succSel (j : Nat) (hj : j < (KeySucc.keys a r L target).length) (k' : RCFive.RowKeys.ThrKey a r L target)
    (hk' : thrKeyAt a r L target (j+1) = some k') (hp : k'.prime.val = 2) (hr : k'.residue.val = 0)
    (hs : thrSeedIdx a r L target k' = 0) :
    thrBase a r four L target NI pub init rcp C cC hF (j+1) =
      Function.update (digBank NI (Bp a r four L target NI pub init rcp C cC hF j 2)
        (RowsConstruction.ThrWidth.T a r four L target) (fun c => dig a r L target k' (c4 c)))
        (masterPort NI 220) (ZeroPadding.pad (Uf r.q (RowsConstruction.ThrWidth.T a r four L target))
          (fb (wT a r four L target) (PCJ45bee56da9f34d5a_StreamPair.radix a r four k'.selection))) := by
  have e0 : thrBase a r four L target NI pub init rcp C cC hF (j+1) =
      workLayout pub init (rowpWords (thrN a r L target) C cC hF) rcp
        (loopBank (thrLive r L) (RT a r four L target) (thrMasters a r four L target (RT a r four L target) k'))
        (c6Words (thrLive r L)ᶜ.card)
        (c5Words (seedWords (thrSeedIdx a r L target k') (NS a r L target))
          (List.replicate (CloseoutFinalC10ThresholdRows.primeCutoff a r target) true) (fun _ => [])
          (seedScratch (NS a r L target))) := by
    simp only [thrBase, hk']
  rw [e0, masters_any a r four L target _ (KeySucc.keys a r L target)[j] k', hr, hp, hs,
    data_digits a r four L target k' 0, data_digits a r four L target k' 1,
    data_digits a r four L target k' 2, data_digits a r four L target k' 3,
    c5_seed_update (thrSeedIdx a r L target (KeySucc.keys a r L target)[j]) 0, wl_c5_update,
    loopBank_update, loopBank_update, loopBank_update, loopBank_update, loopBank_update,
    loopBank_update, loopBank_update, loopBank_update, loopBank_update, loopBank_update,
    wl_loop_update, wl_loop_update, wl_loop_update, wl_loop_update, wl_loop_update,
    wl_loop_update, wl_loop_update, wl_loop_update, wl_loop_update, wl_loop_update,
    Function.update_comm (lp_ne_c5 NI 220 0), Function.update_comm (lp_ne_c5 NI 231 0),
    Function.update_comm (lp_ne_c5 NI 230 0), Function.update_comm (lp_ne_c5 NI 229 0),
    Function.update_comm (lp_ne_c5 NI 228 0), Function.update_comm (lp_ne_c5 NI 209 0),
    Function.update_comm (lp_ne_c5 NI 218 0), Function.update_comm (lp_ne_c5 NI 149 0),
    Function.update_comm (lp_ne_c5 NI 240 0), ← base_eq a r four L target NI pub init rcp C cC hF j hj]
  rfl

end Thr

end
end RowsConstruction.ThrSel
