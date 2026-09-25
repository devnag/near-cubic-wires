import Proof.Packets.PacketsCursorKit
import Proof.Packets.PacketsFieldWidth

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.PacketsGlue.CursorChain
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc NearCubicWires.PacketsGlue.CursorKit
noncomputable section

/-! ## 1. The carry walk -/

/-- The machine's carry walk over `fs` (innermost field first) with FIXED flags `c`. -/
def cascade (c : Fin 8 → Bool) : List (Fin 8) → Digits → Digits
  | [], d => Function.update d 7 (d 7 + 1)
  | f :: fs, d => if c f then cascade c fs (Function.update d f 0) else Function.update d f (d f + 1)

theorem zero_not_mem : ∀ (spec : List (Level (Fin 8))) (d : Digits) (f : Fin 8), f ∉ fields spec →
    zero spec d f = d f
  | [], d, f, _ => rfl
  | l :: ls, d, f, hf => by
    have h1 : f ≠ l.field := fun h => hf (by simp [fields, h])
    have h2 : f ∉ fields ls := fun h => hf (by simp only [fields, List.map_cons, List.mem_cons] at h ⊢; exact Or.inr h)
    show zero ls (Function.update d l.field 0) f = d f
    rw [zero_not_mem ls _ f h2, Function.update_of_ne h1]

theorem zero_mem : ∀ (spec : List (Level (Fin 8))) (d : Digits) (f : Fin 8), f ∈ fields spec →
    zero spec d f = 0
  | [], d, f, hf => by simp [fields] at hf
  | l :: ls, d, f, hf => by
    show zero ls (Function.update d l.field 0) f = 0
    by_cases h2 : f ∈ fields ls
    · exact zero_mem ls _ f h2
    · rw [zero_not_mem ls _ f h2]
      have h1 : f = l.field := by
        simp only [fields, List.map_cons, List.mem_cons] at hf
        rcases hf with h | h
        · exact h
        · exact absurd h h2
      subst h1
      simp

theorem zero_update : ∀ (spec : List (Level (Fin 8))) (d : Digits) (f : Fin 8) (v : ℕ), f ∉ fields spec →
    zero spec (Function.update d f v) = Function.update (zero spec d) f v
  | [], d, f, v, _ => rfl
  | l :: ls, d, f, v, hf => by
    have h1 : f ≠ l.field := fun h => hf (by simp [fields, h])
    have h2 : f ∉ fields ls := fun h => hf (by simp only [fields, List.map_cons, List.mem_cons] at h ⊢; exact Or.inr h)
    show zero ls (Function.update (Function.update d f v) l.field 0) =
      Function.update (zero ls (Function.update d l.field 0)) f v
    rw [Function.update_comm h1, zero_update ls _ f v h2]

/-- **The carry walk over the reversed spec is the successor** (flags from the current digits). -/
theorem cascade_rev (c : Fin 8 → Bool) : ∀ (spec : List (Level (Fin 8))) (d : Digits) (tail : List (Fin 8)),
    WF spec → (∀ l ∈ spec, c l.field = decide (l.bound d ≤ d l.field + 1)) →
    cascade c ((fields spec).reverse ++ tail) d = (next spec d).getD (cascade c tail (zero spec d))
  | [], d, tail, _, _ => rfl
  | l :: ls, d, tail, hwf, hc => by
    obtain ⟨hnot, _, hwf'⟩ := hwf
    have hc' : ∀ l' ∈ ls, c l'.field = decide (l'.bound d ≤ d l'.field + 1) :=
      fun l' hl' => hc l' (List.mem_cons_of_mem _ hl')
    have e1 : (fields (l :: ls)).reverse ++ tail = (fields ls).reverse ++ (l.field :: tail) := by
      simp [fields]
    rw [e1, cascade_rev c ls d (l.field :: tail) hwf' hc']
    have hcl := hc l (List.mem_cons_self ..)
    cases hn : next ls d with
    | some e => rw [next_cons_of_some l ls d e hn]; rfl
    | none =>
      rw [next_cons_of_none l ls d hn]
      have hz : zero ls d l.field = d l.field := zero_not_mem ls d l.field hnot
      simp only [Option.getD_none]
      by_cases hlt : d l.field + 1 < l.bound d
      · have hcf : c l.field = false := by rw [hcl]; simp; omega
        rw [if_pos hlt, Option.getD_some, cascade, hcf, hz]
        simp only [Bool.false_eq_true, if_false]
        exact (zero_update ls d l.field _ hnot).symm
      · have hct : c l.field = true := by rw [hcl]; simp; omega
        rw [if_neg hlt, Option.getD_none, cascade, hct, if_pos rfl]
        show cascade c tail (Function.update (zero ls d) l.field 0) =
          cascade c tail (zero ls (Function.update d l.field 0))
        rw [zero_update ls d l.field 0 hnot]

/-- Radix-1 dummies at the head of the walk change nothing. -/
theorem cascade_dummies (c : Fin 8 → Bool) (fs : List (Fin 8)) : ∀ (D : List (Fin 8)) (d : Digits),
    (∀ g ∈ D, c g = true ∧ d g = 0) → cascade c (D ++ fs) d = cascade c fs d
  | [], d, _ => rfl
  | g :: D, d, h => by
    obtain ⟨hc, hd⟩ := h g (List.mem_cons_self ..)
    show (if c g then cascade c (D ++ fs) (Function.update d g 0) else _) = _
    rw [if_pos hc]
    have e : Function.update d g 0 = d := by rw [← hd]; exact Function.update_eq_self g d
    rw [e]
    exact cascade_dummies c fs D d (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

/-- Radix-1 dummies in the middle of the walk change nothing. -/
theorem cascade_mid (c : Fin 8 → Bool) (D fs : List (Fin 8)) : ∀ (pre : List (Fin 8)) (d : Digits),
    (∀ g ∈ D, c g = true ∧ d g = 0) → cascade c (pre ++ (D ++ fs)) d = cascade c (pre ++ fs) d
  | [], d, h => cascade_dummies c fs D d h
  | p :: pre, d, h => by
    show (if c p then cascade c (pre ++ (D ++ fs)) (Function.update d p 0) else _) =
      (if c p then cascade c (pre ++ fs) (Function.update d p 0) else _)
    by_cases hp : c p = true
    · rw [if_pos hp, if_pos hp]
      refine cascade_mid c D fs pre _ (fun g hg => ⟨(h g hg).1, ?_⟩)
      by_cases hgp : g = p
      · subst hgp; simp
      · rw [Function.update_of_ne hgp]; exact (h g hg).2
    · rw [if_neg hp, if_neg hp]

/-! ## 2. The bounds, the flags and the two fixed field orders -/

/-- Per-circuit bound of coordinate `i` (SYM `bottomCount + 1`, THR `|children|`), `1` past the circuit count. -/
def circBound (a : DecompositionAlgorithm) (i : ℕ) : Request → ℕ
  | .terminal => 1
  | .sym r _ _ _ => if h : i < r.circuits.length then (r.circuits.get ⟨i, h⟩).bottomCount + 1 else 1
  | .thr r _ _ _ => if h : i < r.circuits.length then (ThresholdRows.children a (r.circuits.get ⟨i, h⟩)).length else 1

/-- The bound of field `f` at digits `d` (field 6's bound, the residue's, reads the prime-index digit). -/
def lvlBound (a : DecompositionAlgorithm) (r : Request) (d : Digits) (f : Fin 8) : ℕ :=
  if f.val < 4 then circBound a f.val r else if f.val = 4 then RequestMeta.primeCountOf a r
  else if f.val = 5 then RequestMeta.seedCount a r else primeAt (RequestMeta.cutoffOf a r) (d 4)

/-- The carry flags, from the current digits. -/
def flagsOf (a : DecompositionAlgorithm) (r : Request) (d : Digits) : Fin 8 → Bool :=
  fun f => decide (lvlBound a r d f ≤ d f + 1)

def thrChain : List (Fin 8) := [6, 5, 4, 3, 2, 1, 0]
def symChain : List (Fin 8) := [3, 2, 1, 0, 5]

/-- The reversed coordinate fields, and the dummies in front of them. -/
theorem split4 (n : ℕ) (hn : n ≤ 4) : ([3, 2, 1, 0] : List (Fin 8)) =
    ([3, 2, 1, 0] : List (Fin 8)).take (4 - n) ++ (List.ofFn (fun i : Fin n => (⟨i.val, by omega⟩ : Fin 8))).reverse := by
  interval_cases n <;> rfl

theorem take_mem (n : ℕ) (g : Fin 8) (hg : g ∈ ([3, 2, 1, 0] : List (Fin 8)).take (4 - n)) : n ≤ g.val ∧ g.val < 4 := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp at hg <;> (rcases hg with rfl | rfl | rfl | rfl <;> simp) <;> (subst hg; simp)
  · have : 4 - n = 0 := by omega
    rw [this] at hg; simp at hg

theorem coord_fields (n : ℕ) (h : 0 + n ≤ 8) (bnd : Fin n → ℕ) :
    fields (coordLevels 0 n h bnd) = List.ofFn (fun i : Fin n => (⟨i.val, by omega⟩ : Fin 8)) := by
  simp only [fields, coordLevels, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply]
  apply Fin.ext
  simp

theorem mem_coord {n : ℕ} {h : 0 + n ≤ 8} {bnd : Fin n → ℕ} {l : Level (Fin 8)} (hl : l ∈ coordLevels 0 n h bnd) :
    ∃ i : Fin n, l = (⟨⟨0 + i.val, by omega⟩, fun _ => bnd i⟩ : Level (Fin 8)) := by
  simp only [coordLevels, List.mem_ofFn] at hl
  obtain ⟨i, hi⟩ := hl
  exact ⟨i, hi.symm⟩

/-! ## 3. The walk is the successor on every actual key -/

section Pure
variable (a : DecompositionAlgorithm)

theorem sym_rev (n : ℕ) (hn : n ≤ 4) :
    symChain = ([3, 2, 1, 0] : List (Fin 8)).take (4 - n) ++
      ((List.ofFn (fun i : Fin n => (⟨i.val, by omega⟩ : Fin 8))).reverse ++ [5]) := by
  have hs := split4 n hn
  have e : symChain = ([3, 2, 1, 0] : List (Fin 8)) ++ [5] := rfl
  rw [e]
  conv_lhs => rw [hs]
  rw [List.append_assoc]

theorem sym_fields_rev (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) :
    (fields (cursorSpec a (.sym r four L target))).reverse ++ [] =
      (List.ofFn (fun i : Fin r.circuits.length => (⟨i.val, by omega⟩ : Fin 8))).reverse ++ [5] := by
  simp only [cursorSpec, fields, List.map_cons, List.reverse_cons, List.append_nil]
  have hc := coord_fields r.circuits.length (by omega) (fun i => (r.circuits.get i).bottomCount + 1)
  simp only [fields] at hc
  rw [hc]

theorem thr_rev (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ) :
    thrChain = [6, 5, 4] ++ (([3, 2, 1, 0] : List (Fin 8)).take (4 - r.circuits.length) ++
      (List.ofFn (fun i : Fin r.circuits.length => (⟨i.val, by omega⟩ : Fin 8))).reverse) := by
  have hs := split4 r.circuits.length four
  rw [← hs]
  rfl

theorem thr_fields_rev (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) :
    (fields (cursorSpec a (.thr r four L target))).reverse ++ [] =
      [6, 5, 4] ++ (List.ofFn (fun i : Fin r.circuits.length => (⟨i.val, by omega⟩ : Fin 8))).reverse := by
  simp only [cursorSpec, fields, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.append_nil]
  have hc := coord_fields r.circuits.length (by omega) (fun i => (ThresholdRows.children a (r.circuits.get i)).length)
  simp only [fields] at hc
  rw [hc]
  rfl

/-- The done code is the all-carry end of the walk, on every actual key. -/
theorem done_eq (r : Request) (spec : List (Level (Fin 8))) (d : Digits) (h7 : (7 : Fin 8) ∉ fields spec)
    (hd7 : d 7 = 0) (hout : ∀ f : Fin 8, f ∉ fields spec → f ≠ 7 → d f = 0) :
    cascade (flagsOf a r d) [] (zero spec d) = keyDigits a r none := by
  funext f
  rw [keyDigits_none]
  show Function.update (zero spec d) 7 (zero spec d 7 + 1) f = _
  by_cases hf : f = 7
  · subst hf
    rw [Function.update_self, zero_not_mem spec d 7 h7, hd7]
    simp
  · rw [Function.update_of_ne hf]
    have hv : ¬ f.val = 7 := fun h => hf (Fin.ext h)
    rw [if_neg hv]
    by_cases hm : f ∈ fields spec
    · exact zero_mem spec d f hm
    · rw [zero_not_mem spec d f hm]; exact hout f hm hf

theorem chain_sym (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (k : rcKey a (.sym r four L target)) :
    cascade (flagsOf a (.sym r four L target) (keyDigits a (.sym r four L target) (some k))) symChain
        (keyDigits a (.sym r four L target) (some k)) =
      succDigits a (.sym r four L target) (keyDigits a (.sym r four L target) (some k)) := by
  generalize hd : keyDigits a (.sym r four L target) (some k) = d
  have hdig : ∀ f : Fin 8, d f = if h : f.val < r.circuits.length then k.offset ⟨f.val, h⟩
      else if f.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val else 0 := fun f => by rw [← hd]; rfl
  rw [sym_rev r.circuits.length four, cascade_dummies, ← sym_fields_rev a r four L target]
  · rw [cascade_rev _ _ d [] (cursorSpec_wf a _)]
    · unfold succDigits succD
      congr 1
      apply done_eq a _ _ d
      · intro h7
        simp only [cursorSpec, fields, List.map_cons, List.mem_cons] at h7
        rcases h7 with h | h
        · exact absurd h (by decide)
        · have := mem_fields_coord (h := by omega) h; simp at this; omega
      · rw [hdig]; simp; omega
      · intro f hf h7
        rw [hdig]
        have hn : ¬ f.val < r.circuits.length := by
          intro hl
          apply hf
          simp only [cursorSpec, fields, List.map_cons, List.mem_cons]
          right
          rw [show (coordLevels 0 r.circuits.length (by omega) fun i => (r.circuits.get i).bottomCount + 1).map
            Level.field = fields (coordLevels 0 r.circuits.length (by omega) fun i => (r.circuits.get i).bottomCount + 1)
            from rfl, coord_fields]
          exact List.mem_ofFn.mpr ⟨⟨f.val, hl⟩, rfl⟩
        have h5 : ¬ f.val = 5 := by
          intro h5
          apply hf
          simp only [cursorSpec, fields, List.map_cons, List.mem_cons]
          left; exact Fin.ext h5
        rw [dif_neg hn, if_neg h5]
    · intro l hl
      simp only [cursorSpec, List.mem_cons] at hl
      rcases hl with rfl | hl
      · have hlv : lvlBound a (.sym r four L target) d 5 = RequestMeta.seedCount a (.sym r four L target) := by
          unfold lvlBound
          rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
        simp only [flagsOf, hlv]
        rfl
      · obtain ⟨i, rfl⟩ := mem_coord hl
        have hlv : lvlBound a (.sym r four L target) d ⟨0 + i.val, by omega⟩ = (r.circuits.get i).bottomCount + 1 := by
          unfold lvlBound
          rw [if_pos (show (0 + i.val) < 4 by omega)]
          simp only [circBound]
          rw [dif_pos (show (0 + i.val) < r.circuits.length by omega)]
          simp
        simp only [flagsOf, hlv]
  · intro g hg
    obtain ⟨hn, h4⟩ := take_mem r.circuits.length g hg
    refine ⟨?_, ?_⟩
    · simp only [flagsOf, lvlBound, if_pos h4]
      have hcb : circBound a g.val (.sym r four L target) = 1 := by simp only [circBound]; rw [dif_neg (by omega)]
      rw [hcb, hdig, dif_neg (by omega)]
      have : ¬ g.val = 5 := by omega
      simp [this]
    · rw [hdig, dif_neg (by omega)]
      have : ¬ g.val = 5 := by omega
      simp [this]

theorem chain_thr (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (k : rcKey a (.thr r four L target)) :
    cascade (flagsOf a (.thr r four L target) (keyDigits a (.thr r four L target) (some k))) thrChain
        (keyDigits a (.thr r four L target) (some k)) =
      succDigits a (.thr r four L target) (keyDigits a (.thr r four L target) (some k)) := by
  generalize hd : keyDigits a (.thr r four L target) (some k) = d
  have hdig : ∀ f : Fin 8, d f = if h : f.val < r.circuits.length then (k.selection ⟨f.val, h⟩).val
      else if f.val = 4 then (primeIndexFinEquiv _ k.prime).val
      else if f.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val
      else if f.val = 6 then k.residue.val else 0 := fun f => by rw [← hd]; rfl
  rw [thr_rev r four L target, cascade_mid]
  · rw [← thr_fields_rev a r four L target, cascade_rev _ _ d [] (cursorSpec_wf a _)]
    · unfold succDigits succD
      congr 1
      apply done_eq a _ _ d
      · intro h7
        simp only [cursorSpec, fields, List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at h7
        rcases h7 with h | h | h | h
        · have := mem_fields_coord (h := by omega) h; simp at this; omega
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
      · rw [hdig]; simp; omega
      · intro f hf h7
        rw [hdig]
        have hn : ¬ f.val < r.circuits.length := by
          intro hl
          apply hf
          simp only [cursorSpec, fields, List.map_append, List.mem_append]
          left
          rw [show (coordLevels 0 r.circuits.length (by omega) fun i =>
              (ThresholdRows.children a (r.circuits.get i)).length).map Level.field =
            fields (coordLevels 0 r.circuits.length (by omega) fun i =>
              (ThresholdRows.children a (r.circuits.get i)).length) from rfl, coord_fields]
          exact List.mem_ofFn.mpr ⟨⟨f.val, hl⟩, rfl⟩
        have hmem : ∀ v : ℕ, v = 4 ∨ v = 5 ∨ v = 6 → ¬ f.val = v := by
          intro v hv hfv
          apply hf
          simp only [cursorSpec, fields, List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false]
          right
          rcases hv with rfl | rfl | rfl
          · left; exact Fin.ext hfv
          · right; left; exact Fin.ext hfv
          · right; right; exact Fin.ext hfv
        rw [dif_neg hn, if_neg (hmem 4 (Or.inl rfl)), if_neg (hmem 5 (Or.inr (Or.inl rfl))),
          if_neg (hmem 6 (Or.inr (Or.inr rfl)))]
    · intro l hl
      simp only [cursorSpec, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with hl | rfl | rfl | rfl
      · obtain ⟨i, rfl⟩ := mem_coord hl
        have hlv : lvlBound a (.thr r four L target) d ⟨0 + i.val, by omega⟩ =
            (ThresholdRows.children a (r.circuits.get i)).length := by
          unfold lvlBound
          rw [if_pos (show (0 + i.val) < 4 by omega)]
          simp only [circBound]
          rw [dif_pos (show (0 + i.val) < r.circuits.length by omega)]
          have hi : (⟨0 + i.val, by omega⟩ : Fin r.circuits.length) = i := Fin.ext (Nat.zero_add _)
          rw [hi]
        simp only [flagsOf, hlv]
      · have hlv : lvlBound a (.thr r four L target) d 4 = RequestMeta.primeCountOf a (.thr r four L target) := by
          unfold lvlBound
          rw [if_neg (by decide), if_pos (by decide)]
        simp only [flagsOf, hlv]
        rfl
      · have hlv : lvlBound a (.thr r four L target) d 5 = RequestMeta.seedCount a (.thr r four L target) := by
          unfold lvlBound
          rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
        simp only [flagsOf, hlv]
        rfl
      · have hlv : lvlBound a (.thr r four L target) d 6 =
            primeAt (RequestMeta.cutoffOf a (.thr r four L target)) (d 4) := by
          unfold lvlBound
          rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
        simp only [flagsOf, hlv]
        rfl
  · intro g hg
    obtain ⟨hn, h4⟩ := take_mem r.circuits.length g hg
    refine ⟨?_, ?_⟩
    · simp only [flagsOf, lvlBound, if_pos h4]
      have hcb : circBound a g.val (.thr r four L target) = 1 := by simp only [circBound]; rw [dif_neg (by omega)]
      rw [hcb, hdig, dif_neg (by omega)]
      have h4' : ¬ g.val = 4 := by omega
      have h5 : ¬ g.val = 5 := by omega
      have h6 : ¬ g.val = 6 := by omega
      simp [h4', h5, h6]
    · rw [hdig, dif_neg (by omega)]
      have h4' : ¬ g.val = 4 := by omega
      have h5 : ¬ g.val = 5 := by omega
      have h6 : ¬ g.val = 6 := by omega
      simp [h4', h5, h6]

/-- The field order the machine uses for a request (by the kind flag). -/
def chainOf (r : Request) : List (Fin 8) := if RequestMeta.thrFlag r = 1 then thrChain else symChain

/-- **The walk is the successor** (pure). With the order theorem `succ_spec` this is the cursor's exact duty. -/
theorem chain_succ (r : Request) (k : rcKey a r) :
    cascade (flagsOf a r (keyDigits a r (some k))) (chainOf r) (keyDigits a r (some k)) =
      succDigits a r (keyDigits a r (some k)) := by
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r four L target => exact chain_sym a r four L target k
  | thr r four L target => exact chain_thr a r four L target k

end Pure

/-! ## 4. The chain machine -/

/-- The chain's tapes in an ambient bank of `t` tapes. -/
structure Ports (t : ℕ) where
  port : Fin 8 → Fin t
  flag : Fin 8 → Fin t
  cap : Fin t
  lg : Fin t
  port_inj : Function.Injective port
  cap_lg : cap ≠ lg
  port_cap : ∀ f, port f ≠ cap
  port_lg : ∀ f, port f ≠ lg
  port_flag : ∀ f g, port f ≠ flag g

variable {t : ℕ} (P : Ports t)

def clrSl (f : Fin 8) : Fin 2 → Fin t := ![P.port f, P.lg]
def incSl (f : Fin 8) : Fin 2 → Fin t := ![P.port f, P.cap]

def clrAt (f : Fin 8) := RecoveryFocus.machine (clrSl P f) (MaskedReset.machine Clear.machine (fun _ => true))
def incAt (f : Fin 8) := RecoveryFocus.machine (incSl P f) FramedIncrement.machine

/-- The chain over the field list `fs`. -/
def chainM : List (Fin 8) → (s : ℕ) × Machine t s
  | [] => ⟨_, incAt P 7⟩
  | f :: fs => ⟨_, CloseoutRowsOriginalSwitch.machine (Composition.machine (clrAt P f) (chainM fs).2) (incAt P f)
      (P.flag f)⟩

def chainCost (W : ℕ) : List (Fin 8) → ℕ
  | [] => 4 * W + 2
  | _ :: fs => (2 * (2 * W + 1) + 2) + 1 + chainCost W fs + (4 * W + 2) + 2

theorem focus_at {u s : ℕ} {p : Machine u s} {n : ℕ} {hin hout : Fin u → ℕ}
    {tin tout : Fin u → List Bool} (h : Step p n hin tin hout tout) (slots : Fin u → Fin t)
    (hi : Function.Injective slots) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (install slots A tout) := by
  have h' := h.focus slots hi H A
  rwa [dockH_existing slots H hin hH, install_existing slots A tin hA] at h'

theorem install_update {u : ℕ} (slots : Fin u → Fin t) (hi : Function.Injective slots)
    (A : Fin t → List Bool) (tout : Fin u → List Bool) (j0 : Fin u)
    (h : ∀ j, j ≠ j0 → tout j = A (slots j)) :
    install slots A tout = Function.update A (slots j0) (tout j0) := by
  funext x
  by_cases hx : x = slots j0
  · subst hx
    rw [install_slot _ hi, Function.update_self]
  · rw [Function.update_of_ne hx]
    cases hp : RecoveryFocus.pick slots x with
    | none => simp [install, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [install, hp]
      have hj : j ≠ j0 := fun hj => hx (by rw [← he, hj])
      rw [h j hj, he]

theorem pair_inj {x y : Fin t} (h : x ≠ y) : Function.Injective (![x, y] : Fin 2 → Fin t) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem clr_at (f : Fin 8) (W x R : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hHp : H (P.port f) = 0) (hHl : H P.lg = 0)
    (hX : A (P.port f) = fb W x) (hL : A P.lg = List.replicate R false) (hR : 2 * W + 1 ≤ R) :
    Step (clrAt P f) (2 * (2 * W + 1) + 2) H A H (Function.update A (P.port f) (fb W 0)) := by
  have hs : Function.Injective (clrSl P f) := pair_inj (P.port_lg f)
  have h := focus_at (clr_local W x R hR) (clrSl P f) hs H A
    (fun j => by fin_cases j <;> simp [clrSl, hHp, hHl]) (fun j => by fin_cases j <;> simp [clrSl, hX, hL])
  rw [dockH_existing _ H _ (fun j => by fin_cases j <;> simp [clrSl, hHp, hHl]),
    install_update _ hs A _ 0 (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | simp [clrSl, hL])] at h
  exact h

theorem inc_at (f : Fin 8) (W x R : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hHp : H (P.port f) = 0) (hHc : H P.cap = 0)
    (hX : A (P.port f) = fb W x) (hC : A P.cap = List.replicate R false) (hx : x + 1 < 2 ^ W) (hR : 2 * W ≤ R) :
    Step (incAt P f) (4 * W + 2) H A H (Function.update A (P.port f) (fb W (x + 1))) := by
  have hs : Function.Injective (incSl P f) := pair_inj (P.port_cap f)
  have h := focus_at (inc_local W x R hx hR) (incSl P f) hs H A
    (fun j => by fin_cases j <;> simp [incSl, hHp, hHc]) (fun j => by fin_cases j <;> simp [incSl, hX, hC])
  rw [dockH_existing _ H _ (fun j => by fin_cases j <;> simp [incSl, hHp, hHc]),
    install_update _ hs A _ 0 (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | simp [incSl, hC])] at h
  exact h

/-- **The chain run.** -/
theorem chain_run (W R : ℕ) (c : Fin 8 → Bool) (H : Fin t → ℕ)
    (hHp : ∀ f, H (P.port f) = 0) (hHf : ∀ f, H (P.flag f) = 0) (hHc : H P.cap = 0) (hHl : H P.lg = 0)
    (hR : 2 * W + 1 ≤ R) :
    ∀ (fs : List (Fin 8)) (A : Fin t → List Bool) (e : Digits),
      (∀ f, A (P.port f) = fb W (e f)) → (∀ f ∈ fs, readTapeBit (A (P.flag f)) 0 = c f) →
      A P.cap = List.replicate R false → A P.lg = List.replicate R false → (∀ f, e f + 1 < 2 ^ W) →
      ∃ A' : Fin t → List Bool, Step (chainM P fs).2 (chainCost W fs) H A H A' ∧
        (∀ f, A' (P.port f) = fb W (cascade c fs e f)) ∧ (∀ i, (∀ f, P.port f ≠ i) → A' i = A i)
  | [], A, e, hP, _, hC, hL, hfit => by
    refine ⟨_, inc_at P 7 W (e 7) R H A (hHp 7) hHc (hP 7) hC (hfit 7) (by omega), ?_, ?_⟩
    · intro f
      by_cases hf : f = 7
      · subst hf; simp [cascade]
      · rw [Function.update_of_ne (fun h => hf (P.port_inj h)), hP f]
        simp [cascade, Function.update_of_ne hf]
    · intro i hi
      rw [Function.update_of_ne (fun h => hi 7 h.symm)]
  | f :: fs, A, e, hP, hF, hC, hL, hfit => by
    have hread := hF f (List.mem_cons_self ..)
    cases hcf : c f with
    | true =>
      have s1 := clr_at P f W (e f) R H A (hHp f) hHl (hP f) hL hR
      set A1 := Function.update A (P.port f) (fb W 0) with hA1
      have hW : 1 < 2 ^ W := by have := hfit f; omega
      obtain ⟨A', s2, hp', ho'⟩ := chain_run W R c H hHp hHf hHc hHl hR fs A1 (Function.update e f 0)
        (by
          intro g
          by_cases hg : g = f
          · subst hg; simp [hA1]
          · rw [hA1, Function.update_of_ne (fun h => hg (P.port_inj h)), hP g, Function.update_of_ne hg])
        (by
          intro g hg
          rw [hA1, Function.update_of_ne (fun h => P.port_flag f g h.symm)]
          exact hF g (List.mem_cons_of_mem _ hg))
        (by rw [hA1, Function.update_of_ne (fun h => P.port_cap f h.symm)]; exact hC)
        (by rw [hA1, Function.update_of_ne (fun h => P.port_lg f h.symm)]; exact hL)
        (by
          intro g
          by_cases hg : g = f
          · subst hg; rw [Function.update_self]; omega
          · rw [Function.update_of_ne hg]; exact hfit g)
      have s3 := CloseoutRowsOriginalSwitch.true_run (Composition.machine (clrAt P f) (chainM P fs).2) (incAt P f)
        (P.flag f) (s1.seq s2) (by rw [hHf f, hread, hcf])
      refine ⟨A', s3.enlarge (by simp only [chainCost]; omega), ?_, ?_⟩
      · intro g
        rw [hp' g]
        simp [cascade, hcf]
      · intro i hi
        rw [ho' i hi, hA1, Function.update_of_ne (fun h => hi f h.symm)]
    | false =>
      have s1 := inc_at P f W (e f) R H A (hHp f) hHc (hP f) hC (hfit f) (by omega)
      have s3 := CloseoutRowsOriginalSwitch.false_run (Composition.machine (clrAt P f) (chainM P fs).2) (incAt P f)
        (P.flag f) s1 (by rw [hHf f, hread, hcf])
      refine ⟨_, s3.enlarge (by simp only [chainCost]; omega), ?_, ?_⟩
      · intro g
        by_cases hg : g = f
        · subst hg; simp [cascade, hcf]
        · rw [Function.update_of_ne (fun h => hg (P.port_inj h)), hP g]
          simp [cascade, hcf, Function.update_of_ne hg]
      · intro i hi
        rw [Function.update_of_ne (fun h => hi f h.symm)]

end
end NearCubicWires.PacketsGlue.CursorChain

