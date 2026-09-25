import Proof.Packets.PacketsCombineThrWord
import Proof.Packets.PacketsSymExact
import Proof.Packets.PacketsMetaKeyDecode

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsKeys.Stage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsMeta NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsSymBits
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## Request kinds and the restricted shapes -/

/-- SYM requests. -/
def IsSym : Request → Prop
  | .sym _ _ _ _ => True
  | _ => False

/-- THR requests. -/
def IsThr : Request → Prop
  | .thr _ _ _ _ => True
  | _ => False

structure KeyStageOn (a : DecompositionAlgorithm) (p : Request → Prop)
    (v : ∀ r : Request, rcKey a r → ℕ → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (11 + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  run : ∀ r, p r → ∀ (k : rcKey a r), k ∈ rcKeys a r → ∀ j, j < maskCount a r k →
    ∃ (H : Fin (11 + extra) → ℕ) (A : Fin (11 + extra) → List Bool),
      Step machine (cost r) (fun _ => 0) (keyEntry a r k j (11 + extra)) H A ∧
      (∀ i : Fin (11 + extra), i.val < 10 → A i = keyEntry a r k j (11 + extra) i ∧ H i = 0) ∧
      A ⟨10, by omega⟩ = v r k j ∧ H ⟨10, by omega⟩ = 0

structure KeyWordOn (a : DecompositionAlgorithm) (p : Request → Prop) (v : ∀ r : Request, rcKey a r → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (10 + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  run : ∀ r, p r → ∀ (k : rcKey a r), k ∈ rcKeys a r →
    ∃ (H : Fin (10 + extra) → ℕ) (A : Fin (10 + extra) → List Bool),
      Step machine (cost r) (fun _ => 0) (PacketsCombine.metaEntry a r (some k) (10 + extra)) H A ∧
      (∀ i : Fin (10 + extra), i.val < 9 → A i = PacketsCombine.metaEntry a r (some k) (10 + extra) i ∧ H i = 0) ∧
      A ⟨9, by omega⟩ = v r k ∧ H ⟨9, by omega⟩ = 0

/-- **`m` key-level words** on tapes `9..8+m` (one fixed machine), tapes 0–8 kept, for requests satisfying `p`. -/
structure KVecOn (a : DecompositionAlgorithm) (p : Request → Prop) (m : ℕ)
    (outs : ℕ → ∀ r : Request, rcKey a r → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (9 + m + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  run : ∀ r, p r → ∀ (k : rcKey a r), k ∈ rcKeys a r →
    ∃ (H : Fin (9 + m + extra) → ℕ) (A : Fin (9 + m + extra) → List Bool),
      Step machine (cost r) (fun _ => 0) (PacketsCombine.metaEntry a r (some k) (9 + m + extra)) H A ∧
      (∀ i : Fin (9 + m + extra), i.val < 9 →
        A i = PacketsCombine.metaEntry a r (some k) (9 + m + extra) i ∧ H i = 0) ∧
      ∀ t (ht : t < m), A ⟨9 + t, by omega⟩ = outs t r k ∧ H ⟨9 + t, by omega⟩ = 0

variable {a : DecompositionAlgorithm}

/-! ## Adapters -/

/-- A THR word family, read at any request (`[]` off THR). -/
def thrOuts (outs : ℕ → PacketsCombine.Asm.TVal a) : ℕ → ∀ r : Request, rcKey a r → List Bool
  | t, .thr r four L target, k => outs t r four L target k
  | _, .sym _ _ _ _, _ => []
  | _, .terminal, _ => []

def KVecOn.ofThrVec {m : ℕ} {outs : ℕ → PacketsCombine.Asm.TVal a} (V : PacketsCombine.Asm.ThrVec a m outs) :
    KVecOn a IsThr m (thrOuts outs) where
  extra := V.extra
  states := V.states
  machine := V.machine
  cost := V.cost
  costC := V.costC
  costD := V.costD
  cost_le := V.cost_le
  run := by
    intro r hp k hk
    cases r with
    | terminal => exact hp.elim
    | sym _ _ _ _ => exact hp.elim
    | thr r0 four L target =>
      obtain ⟨H, A, st, keep, out⟩ := V.run r0 four L target k hk
      exact ⟨H, A, st, keep, out⟩

def KVecOn.ofKeyWord (p : Request → Prop) {w : ∀ r : Request, rcKey a r → List Bool} (s : KeyWord a w) :
    KVecOn a p 1 (fun _ => w) where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  costC := s.costC
  costD := s.costD
  cost_le := s.cost_le
  run := by
    intro r _ k hk
    obtain ⟨H, A, st, keep, h9, hh9⟩ := s.run r k hk
    refine ⟨H, A, st, keep, ?_⟩
    · intro t ht
      have ht0 : t = 0 := by omega
      subst ht0
      exact ⟨h9, hh9⟩

/-! ## The key-stage entry bank -/

theorem ke_val (r : Request) (k : rcKey a r) (j : ℕ) {t u : ℕ} (i : Fin t) (i' : Fin u) (h : i.val = i'.val) :
    keyEntry a r k j t i = keyEntry a r k j u i' := by
  unfold keyEntry PacketsCombine.metaEntry
  simp only [h]

theorem ke_meta (r : Request) (k : rcKey a r) (j : ℕ) {t u : ℕ} (i : Fin t) (i' : Fin u) (h : i.val = i'.val)
    (h9 : i.val < 9) : keyEntry a r k j t i = PacketsCombine.metaEntry a r (some k) u i' := by
  unfold keyEntry PacketsCombine.metaEntry
  simp only [h]
  rw [if_neg (by omega)]

theorem ke_nine (r : Request) (k : rcKey a r) (j : ℕ) {t : ℕ} (i : Fin t) (h : i.val = 9) :
    keyEntry a r k j t i = List.replicate j true := by
  unfold keyEntry
  rw [if_pos h]

theorem ke_high (r : Request) (k : rcKey a r) (j : ℕ) {t : ℕ} (i : Fin t) (h : 10 ≤ i.val) :
    keyEntry a r k j t i = [] := by
  unfold keyEntry PacketsCombine.metaEntry
  rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

theorem me_high (r : Request) (c : Option (rcKey a r)) {t : ℕ} (i : Fin t) (h : 9 ≤ i.val) :
    PacketsCombine.metaEntry a r c t i = [] := by
  unfold PacketsCombine.metaEntry
  rw [if_neg (by omega), dif_neg (by omega)]

/-! ## Slot maps of the assembly -/

section Slots
variable (m u e : ℕ) (wslot : Fin m → Fin u)

/-- The vector: key tapes stay, word `t` goes to the program's slot `wslot t`, private tapes past the program. -/
def vmap (i : Fin (9 + m + e)) : Fin (11 + (u + e)) :=
  if h : i.val < 9 then ⟨i.val, by omega⟩
  else if h2 : i.val < 9 + m then ⟨11 + (wslot ⟨i.val - 9, by omega⟩).val, by
      have := (wslot ⟨i.val - 9, by omega⟩).isLt; omega⟩
  else ⟨11 + u + (i.val - 9 - m), by omega⟩

theorem vmap_lt (i : Fin (9 + m + e)) (h : i.val < 9) : (vmap m u e wslot i).val = i.val := by
  unfold vmap; rw [dif_pos h]

theorem vmap_mid (i : Fin (9 + m + e)) (h1 : 9 ≤ i.val) (h2 : i.val < 9 + m) :
    (vmap m u e wslot i).val = 11 + (wslot ⟨i.val - 9, by omega⟩).val := by
  unfold vmap; rw [dif_neg (by omega), dif_pos h2]

theorem vmap_hi (i : Fin (9 + m + e)) (h : 9 + m ≤ i.val) : (vmap m u e wslot i).val = 11 + u + (i.val - 9 - m) := by
  unfold vmap; rw [dif_neg (by omega), dif_neg (by omega)]

theorem vmap_inj (hw : Function.Injective wslot) : Function.Injective (vmap m u e wslot) := by
  intro i i' h
  have hv := congrArg Fin.val h
  apply Fin.ext
  rcases Nat.lt_or_ge i.val 9 with a1 | a1 <;> rcases Nat.lt_or_ge i'.val 9 with b1 | b1
  · rwa [vmap_lt _ _ _ _ _ a1, vmap_lt _ _ _ _ _ b1] at hv
  · rw [vmap_lt _ _ _ _ _ a1] at hv
    rcases Nat.lt_or_ge i'.val (9 + m) with b2 | b2
    · rw [vmap_mid _ _ _ _ _ b1 b2] at hv; omega
    · rw [vmap_hi _ _ _ _ _ b2] at hv; omega
  · rw [vmap_lt _ _ _ _ _ b1] at hv
    rcases Nat.lt_or_ge i.val (9 + m) with a2 | a2
    · rw [vmap_mid _ _ _ _ _ a1 a2] at hv; omega
    · rw [vmap_hi _ _ _ _ _ a2] at hv; omega
  · rcases Nat.lt_or_ge i.val (9 + m) with a2 | a2 <;> rcases Nat.lt_or_ge i'.val (9 + m) with b2 | b2
    · rw [vmap_mid _ _ _ _ _ a1 a2, vmap_mid _ _ _ _ _ b1 b2] at hv
      have := hw (Fin.ext (by omega : (wslot ⟨i.val - 9, by omega⟩).val = (wslot ⟨i'.val - 9, by omega⟩).val))
      have := congrArg Fin.val this
      simp only at this
      omega
    · rw [vmap_mid _ _ _ _ _ a1 a2, vmap_hi _ _ _ _ _ b2] at hv
      have := (wslot ⟨i.val - 9, by omega⟩).isLt; omega
    · rw [vmap_hi _ _ _ _ _ a2, vmap_mid _ _ _ _ _ b1 b2] at hv
      have := (wslot ⟨i'.val - 9, by omega⟩).isLt; omega
    · rw [vmap_hi _ _ _ _ _ a2, vmap_hi _ _ _ _ _ b2] at hv; omega

/-- `UCopy`: the unary `1^j` (tape 9) into the program's `j`-stream slot. -/
def umap (jslot : Fin u) : Fin 2 → Fin (11 + (u + e)) :=
  ![⟨9, by omega⟩, ⟨11 + jslot.val, by have := jslot.isLt; omega⟩]

theorem umap_inj (jslot : Fin u) : Function.Injective (umap u e jslot) := by
  intro i i' h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases i' <;> simp [umap] at hv ⊢ <;> omega

/-- The program: local tape `i` at `11 + i`. -/
def pmap (i : Fin u) : Fin (11 + (u + e)) := ⟨11 + i.val, by omega⟩

theorem pmap_inj : Function.Injective (pmap u e) := by
  intro i i' h
  have hv := congrArg Fin.val h
  simp only [pmap] at hv
  exact Fin.ext (by omega)

/-- The exact copy: the program's output stream and marks onto tape 10. -/
def emap (oslot mslot : Fin u) : Fin 3 → Fin (11 + (u + e)) :=
  ![⟨11 + oslot.val, by have := oslot.isLt; omega⟩, ⟨11 + mslot.val, by have := mslot.isLt; omega⟩, ⟨10, by omega⟩]

theorem emap_inj (oslot mslot : Fin u) (h : oslot ≠ mslot) : Function.Injective (emap u e oslot mslot) := by
  intro i i' hh
  have hv := congrArg Fin.val hh
  have hne : oslot.val ≠ mslot.val := fun e => h (Fin.ext e)
  fin_cases i <;> fin_cases i' <;> simp [emap] at hv ⊢ <;> omega

end Slots

/-! ## The assembly -/

section Assembly
variable {p : Request → Prop} {m : ℕ} {outs : ℕ → ∀ r : Request, rcKey a r → List Bool}
  {v : ∀ r : Request, rcKey a r → ℕ → List Bool}
  (V : KVecOn a p m outs) {u s : ℕ} (P : Machine u s) (wslot : Fin m → Fin u) (jslot oslot mslot : Fin u)

/-- The core: vector, `UCopy`, program, exact copy. -/
def core :=
  Composition.machine (RecoveryFocus.machine (vmap m u V.extra wslot) V.machine)
    (Composition.machine (RecoveryFocus.machine (umap u V.extra jslot) UCopy.machine)
      (Composition.machine (RecoveryFocus.machine (pmap u V.extra) P)
        (RecoveryFocus.machine (emap u V.extra oslot mslot) ExactCopy.machine)))

/-! ### Tapes outside a slot map -/

theorem vmap_ne_low (i : Fin (11 + (u + V.extra))) (h1 : 9 ≤ i.val) (h2 : i.val < 11) :
    ∀ l, vmap m u V.extra wslot l ≠ i := by
  intro l hl
  have hv := congrArg Fin.val hl
  rcases Nat.lt_or_ge l.val 9 with a1 | a1
  · rw [vmap_lt _ _ _ _ _ a1] at hv; omega
  · rcases Nat.lt_or_ge l.val (9 + m) with a2 | a2
    · rw [vmap_mid _ _ _ _ _ a1 a2] at hv; omega
    · rw [vmap_hi _ _ _ _ _ a2] at hv; omega

theorem vmap_ne_loc (x : Fin u) (hx : ∀ t, wslot t ≠ x) : ∀ l, vmap m u V.extra wslot l ≠ pmap u V.extra x := by
  intro l hl
  have hv := congrArg Fin.val hl
  simp only [pmap] at hv
  rcases Nat.lt_or_ge l.val 9 with a1 | a1
  · rw [vmap_lt _ _ _ _ _ a1] at hv; omega
  · rcases Nat.lt_or_ge l.val (9 + m) with a2 | a2
    · rw [vmap_mid _ _ _ _ _ a1 a2] at hv
      exact hx ⟨l.val - 9, by omega⟩ (Fin.ext (by omega))
    · rw [vmap_hi _ _ _ _ _ a2] at hv; have := x.isLt; omega

theorem umap_ne (i : Fin (11 + (u + V.extra))) (h1 : i.val ≠ 9) (h2 : i.val ≠ 11 + jslot.val) :
    ∀ l, umap u V.extra jslot l ≠ i := by
  intro l hl
  have hv := congrArg Fin.val hl
  fin_cases l <;> simp [umap] at hv <;> omega

theorem pmap_ne (i : Fin (11 + (u + V.extra))) (h : i.val < 11) : ∀ l, pmap u V.extra l ≠ i := by
  intro l hl
  have hv := congrArg Fin.val hl
  simp only [pmap] at hv
  omega

theorem emap_ne (i : Fin (11 + (u + V.extra))) (h1 : i.val ≠ 10) (h2 : i.val ≠ 11 + oslot.val)
    (h3 : i.val ≠ 11 + mslot.val) : ∀ l, emap u V.extra oslot mslot l ≠ i := by
  intro l hl
  have hv := congrArg Fin.val hl
  fin_cases l <;> simp [emap] at hv <;> omega

/-! ### The run of the core -/

theorem core_run (hw : Function.Injective wslot) (hjw : ∀ t, wslot t ≠ jslot) (hom : oslot ≠ mslot)
    (r : Request) (hp : p r) (k : rcKey a r) (hk : k ∈ rcKeys a r) (j : ℕ) (W n : ℕ) (σin σ' : Fin u → TS)
    (vr : List Bool) (hl : LRuns W P n σin σ') (ho : σ' oslot = .cells (sf vr) 1)
    (hm : σ' mslot = .cells (sf (List.replicate vr.length true)) 1)
    (hwr : ∀ t, σin (wslot t) = .cells (fun i => readTapeBit (outs t.val r k) i) 0)
    (hjr : σin jslot = .cells (sf (List.replicate (j + 1) true)) 1)
    (hbr : ∀ i : Fin u, (∀ t, wslot t ≠ i) → i ≠ jslot → TR W (σin i) 0 []) :
    ∃ (H : Fin (11 + (u + V.extra)) → ℕ) (A : Fin (11 + (u + V.extra)) → List Bool),
      Step (core V P wslot jslot oslot mslot) (V.cost r + 1 + (2 * j + 4 + 1 + (n + 1 + (vr.length + 1))))
        (fun _ => 0) (keyEntry a r k j (11 + (u + V.extra))) H A ∧
      (∀ i : Fin (11 + (u + V.extra)), i.val < 10 → A i = keyEntry a r k j (11 + (u + V.extra)) i) ∧
      A ⟨10, by omega⟩ = vr := by
  set N := 11 + (u + V.extra) with hN
  set E0 := keyEntry a r k j N with hE0
  obtain ⟨H1, A1, st1, keep1, out1⟩ := V.run r hp k hk
  -- the vector
  obtain ⟨H2, A2, st2, hs2, ho2⟩ := Dock.lift st1 (vmap m u V.extra wslot) (vmap_inj m u V.extra wslot hw)
    (fun _ => 0) (fun _ => 0) E0 (by
      intro i
      refine ⟨rfl, ?_⟩
      rw [ZeroPadding.pad_zero]
      by_cases h9 : i.val < 9
      · exact ke_meta r k j _ _ (vmap_lt _ _ _ _ _ h9) (by rw [vmap_lt _ _ _ _ _ h9]; exact h9)
      · rw [hE0, ke_high r k j _ (by
          rcases Nat.lt_or_ge i.val (9 + m) with a2 | a2
          · rw [vmap_mid _ _ _ _ _ (by omega) a2]; omega
          · rw [vmap_hi _ _ _ _ _ a2]; omega), me_high r _ _ (by omega)])
  -- `1^j` into the `j`-stream
  have h9 : ∀ l, vmap m u V.extra wslot l ≠ ⟨9, by omega⟩ := vmap_ne_low V wslot _ (by simp) (by simp)
  have hjl : ∀ l, vmap m u V.extra wslot l ≠ pmap u V.extra jslot := vmap_ne_loc V wslot jslot (fun t => hjw t)
  have f0 : H2 (umap u V.extra jslot 0) = (![0, 0] : Fin 2 → ℕ) 0 ∧
      A2 (umap u V.extra jslot 0) = ZeroPadding.pad 0 ((![List.replicate j true, []] : Fin 2 → List Bool) 0) := by
    obtain ⟨e1, e2⟩ := ho2 _ h9
    refine ⟨e1, ?_⟩
    rw [ZeroPadding.pad_zero, show umap u V.extra jslot 0 = ⟨9, by omega⟩ from rfl, e2]
    exact ke_nine r k j _ rfl
  have f1 : H2 (umap u V.extra jslot 1) = (![0, 0] : Fin 2 → ℕ) 1 ∧
      A2 (umap u V.extra jslot 1) = ZeroPadding.pad 0 ((![List.replicate j true, []] : Fin 2 → List Bool) 1) := by
    obtain ⟨e1, e2⟩ := ho2 _ hjl
    refine ⟨e1, ?_⟩
    rw [ZeroPadding.pad_zero, show umap u V.extra jslot 1 = pmap u V.extra jslot from rfl, e2]
    exact ke_high r k j _ (by simp only [pmap]; omega)
  obtain ⟨H3, A3, st3, hs3, ho3⟩ := Dock.lift (UCopy.run j) (umap u V.extra jslot) (umap_inj u V.extra jslot)
    (fun _ => 0) H2 A2 (by
      intro i
      fin_cases i
      · exact f0
      · exact f1)
  -- the program's entry
  have hloc : ∀ i : Fin u, TR W (σin i) (H3 (pmap u V.extra i)) (A3 (pmap u V.extra i)) := by
    intro i
    by_cases hi : ∃ t, wslot t = i
    · obtain ⟨t, rfl⟩ := hi
      have hu : ∀ l, umap u V.extra jslot l ≠ pmap u V.extra (wslot t) := umap_ne V jslot _
        (by simp only [pmap]; omega) (by
          simp only [pmap]
          intro h
          exact hjw t (Fin.ext (by omega)))
      obtain ⟨e1, e2⟩ := ho3 _ hu
      have ev : pmap u V.extra (wslot t) = vmap m u V.extra wslot ⟨9 + t.val, by omega⟩ :=
        Fin.ext (by rw [vmap_mid _ _ _ _ _ (by simp) (by simp)]; simp [pmap])
      rw [e1, e2, ev, (hs2 _).1, (hs2 _).2, ZeroPadding.pad_zero, (out1 t.val t.isLt).1,
        (out1 t.val t.isLt).2, hwr t]
      exact ⟨rfl, fun _ => rfl⟩
    · by_cases hj : i = jslot
      · subst hj
        have e : pmap u V.extra i = umap u V.extra i 1 := rfl
        rw [e, (hs3 1).1, (hs3 1).2, ZeroPadding.pad_zero, hjr]
        exact ⟨rfl, fun _ => rfl⟩
      · have hn : ∀ t, wslot t ≠ i := fun t ht => hi ⟨t, ht⟩
        have hu : ∀ l, umap u V.extra jslot l ≠ pmap u V.extra i := umap_ne V jslot _
          (by simp only [pmap]; omega) (by
            simp only [pmap]
            intro h
            exact hj (Fin.ext (by omega)))
        obtain ⟨e1, e2⟩ := ho3 _ hu
        obtain ⟨f1, f2⟩ := ho2 _ (vmap_ne_loc V wslot i hn)
        rw [e1, e2, f1, f2, hE0, ke_high r k j _ (by simp only [pmap]; omega)]
        exact hbr i hn hj
  obtain ⟨Hl, Al, stp, trs⟩ := hl (fun i => H3 (pmap u V.extra i)) (fun i => A3 (pmap u V.extra i)) hloc
  obtain ⟨H4, A4, st4, hs4, ho4⟩ := Dock.lift stp (pmap u V.extra) (pmap_inj u V.extra) (fun _ => 0) H3 A3
    (fun i => ⟨rfl, (ZeroPadding.pad_zero _).symm⟩)
  -- the exact copy
  have tro := trs oslot
  rw [ho] at tro
  have tm := trs mslot
  rw [hm] at tm
  obtain ⟨to1, to2⟩ := tro
  obtain ⟨tm1, tm2⟩ := tm
  have h10 : ∀ l, pmap u V.extra l ≠ ⟨10, by omega⟩ := pmap_ne V _ (by simp)
  have hu10 : ∀ l, umap u V.extra jslot l ≠ ⟨10, by omega⟩ := umap_ne V jslot _ (by simp) (by simp only; omega)
  have hv10 : ∀ l, vmap m u V.extra wslot l ≠ ⟨10, by omega⟩ := vmap_ne_low V wslot _ (by simp) (by simp)
  have g0 : H4 (emap u V.extra oslot mslot 0) = (![1, 1, ([] : List Bool).length] : Fin 3 → ℕ) 0 ∧
      A4 (emap u V.extra oslot mslot 0) =
        ZeroPadding.pad 0 ((![Al oslot, Al mslot, []] : Fin 3 → List Bool) 0) := by
    have e : emap u V.extra oslot mslot 0 = pmap u V.extra oslot := rfl
    rw [e, (hs4 _).1, (hs4 _).2, to1]
    exact ⟨rfl, rfl⟩
  have g1 : H4 (emap u V.extra oslot mslot 1) = (![1, 1, ([] : List Bool).length] : Fin 3 → ℕ) 1 ∧
      A4 (emap u V.extra oslot mslot 1) =
        ZeroPadding.pad 0 ((![Al oslot, Al mslot, []] : Fin 3 → List Bool) 1) := by
    have e : emap u V.extra oslot mslot 1 = pmap u V.extra mslot := rfl
    rw [e, (hs4 _).1, (hs4 _).2, tm1]
    exact ⟨rfl, rfl⟩
  have g2 : H4 (emap u V.extra oslot mslot 2) = (![1, 1, ([] : List Bool).length] : Fin 3 → ℕ) 2 ∧
      A4 (emap u V.extra oslot mslot 2) =
        ZeroPadding.pad 0 ((![Al oslot, Al mslot, []] : Fin 3 → List Bool) 2) := by
    have e : emap u V.extra oslot mslot 2 = ⟨10, by omega⟩ := rfl
    rw [e, (ho4 _ h10).1, (ho4 _ h10).2, (ho3 _ hu10).1, (ho3 _ hu10).2, (ho2 _ hv10).1, (ho2 _ hv10).2,
      hE0, ke_high r k j _ (by simp)]
    exact ⟨rfl, rfl⟩
  obtain ⟨H5, A5, st5, hs5, ho5⟩ := Dock.lift (ExactCopy.run (Al oslot) (Al mslot) [] vr to2 tm2)
    (emap u V.extra oslot mslot) (emap_inj u V.extra oslot mslot hom) (fun _ => 0) H4 A4 (by
      intro i
      fin_cases i
      · exact g0
      · exact g1
      · exact g2)
  refine ⟨H5, A5, st2.seq (st3.seq (st4.seq st5)), ?_, ?_⟩
  · intro i hi
    have he : ∀ l, emap u V.extra oslot mslot l ≠ i := emap_ne V oslot mslot i (by omega) (by omega) (by omega)
    have hp4 : ∀ l, pmap u V.extra l ≠ i := pmap_ne V i (by omega)
    rw [(ho5 _ he).2, (ho4 _ hp4).2]
    by_cases hi9 : i.val = 9
    · have e : i = umap u V.extra jslot 0 := Fin.ext (by simp [umap, hi9])
      rw [e, (hs3 0).2, ZeroPadding.pad_zero]
      exact (ke_nine r k j _ rfl).symm
    · have hu : ∀ l, umap u V.extra jslot l ≠ i := umap_ne V jslot i hi9 (by omega)
      rw [(ho3 _ hu).2]
      have hi9' : i.val < 9 := by omega
      have e : i = vmap m u V.extra wslot ⟨i.val, by omega⟩ := Fin.ext (by rw [vmap_lt _ _ _ _ _ hi9'])
      rw [e, (hs2 _).2, ZeroPadding.pad_zero, (keep1 _ hi9').1]
      exact (ke_meta r k j (vmap m u V.extra wslot ⟨i.val, by omega⟩) ⟨i.val, by omega⟩
        (vmap_lt _ _ _ _ _ hi9') (by rw [vmap_lt _ _ _ _ _ hi9']; exact hi9')).symm
  · have e : (⟨10, by omega⟩ : Fin N) = emap u V.extra oslot mslot 2 := rfl
    rw [e, (hs5 2).2, ZeroPadding.pad_zero]
    rfl

def KeyStageOn.ofProg (hw : Function.Injective wslot) (hjw : ∀ t, wslot t ≠ jslot) (hom : oslot ≠ mslot)
    (Wd pn : ∀ r : Request, rcKey a r → ℕ → ℕ) (σin : ∀ r : Request, rcKey a r → ℕ → Fin u → TS)
    (hrun : ∀ r, p r → ∀ k, k ∈ rcKeys a r → ∀ j, j < maskCount a r k → ∃ σ' : Fin u → TS,
      LRuns (Wd r k j) P (pn r k j) (σin r k j) σ' ∧ σ' oslot = .cells (sf (v r k j)) 1 ∧
      σ' mslot = .cells (sf (List.replicate (v r k j).length true)) 1)
    (hwr : ∀ r k j t, σin r k j (wslot t) = .cells (fun i => readTapeBit (outs t.val r k) i) 0)
    (hjr : ∀ r k j, σin r k j jslot = .cells (sf (List.replicate (j + 1) true)) 1)
    (hbr : ∀ r k j (i : Fin u), (∀ t, wslot t ≠ i) → i ≠ jslot → TR (Wd r k j) (σin r k j i) 0 [])
    (pc : Request → ℕ) (hpc : ∀ r, p r → ∀ k, k ∈ rcKeys a r → ∀ j, j < maskCount a r k →
      2 * j + 4 + 1 + (pn r k j + 1 + ((v r k j).length + 1)) ≤ pc r)
    (cC cD : ℕ) (hcC : ∀ r, pc r ≤ cC * (r.smallSize a) ^ cD) : KeyStageOn a p v where
  extra := u + V.extra + 1
  states := _
  machine := MaskedReset.machine (core V P wslot jslot oslot mslot) (fun _ => true)
  cost := fun r => 2 * (V.cost r + 1 + pc r) + 2
  costC := 2 * (V.costC + 1 + cC) + 2
  costD := V.costD + cD
  cost_le := by
    intro r
    have h := PacketsCombine.Asm.sum_le _ _ _ _ _ _ _ (one_le_small a r) (V.cost_le r) (hcC r)
    have hs := one_le_small a r
    have p0 : 1 ≤ (r.smallSize a) ^ (V.costD + cD) := Nat.one_le_pow _ _ hs
    have e : (2 * (V.costC + 1 + cC) + 2) * (r.smallSize a) ^ (V.costD + cD) =
        2 * ((V.costC + 1 + cC) * (r.smallSize a) ^ (V.costD + cD)) + 2 * (r.smallSize a) ^ (V.costD + cD) := by
      ring
    show 2 * (V.cost r + 1 + pc r) + 2 ≤ _
    rw [e]
    omega
  run := by
    intro r hp k hk j hj
    obtain ⟨σ', hl, ho, hm⟩ := hrun r hp k hk j hj
    obtain ⟨H, A, st, keep, out⟩ := core_run V P wslot jslot oslot mslot hw hjw hom r hp k hk j (Wd r k j)
      (pn r k j) (σin r k j) σ' (v r k j) hl ho hm (hwr r k j) (hjr r k j) (hbr r k j)
    have st' := st.enlarge (show _ ≤ V.cost r + 1 + pc r from by have := hpc r hp k hk j hj; omega)
    obtain ⟨kk, hmk⟩ := step_mask0 st' (fun _ => true) (fun _ _ => rfl)
    have eH : (fun i => Fin.addCases (fun _ : Fin (11 + (u + V.extra)) => (0 : ℕ)) (fun _ : Fin 1 => 0) i) =
        (fun _ : Fin (11 + (u + V.extra) + 1) => (0 : ℕ)) := by
      funext i
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
      · rw [Fin.addCases_left]
      · rw [Fin.addCases_right]
    have eA : (fun i => Fin.addCases (keyEntry a r k j (11 + (u + V.extra))) (fun _ : Fin 1 => ([] : List Bool)) i) =
        keyEntry a r k j (11 + (u + V.extra) + 1) := by
      funext i
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
      · rw [Fin.addCases_left]
        exact ke_val r k j _ _ rfl
      · rw [Fin.addCases_right, ke_high r k j _ (by simp; omega)]
    rw [eH, eA] at hmk
    refine ⟨_, _, hmk, ?_, ?_, ?_⟩
    · intro i hi
      have e : i = Fin.castAdd 1 (⟨i.val, by omega⟩ : Fin (11 + (u + V.extra))) := Fin.ext rfl
      rw [e, Fin.addCases_left, Fin.addCases_left]
      refine ⟨(keep _ hi).trans (ke_val r k j _ _ rfl), ?_⟩
      simp
    · have e : (⟨10, by omega⟩ : Fin (11 + (u + V.extra) + 1)) = Fin.castAdd 1 (⟨10, by omega⟩ : Fin (11 + (u + V.extra))) :=
        Fin.ext rfl
      rw [e, Fin.addCases_left]
      exact out
    · have e : (⟨10, by omega⟩ : Fin (11 + (u + V.extra) + 1)) = Fin.castAdd 1 (⟨10, by omega⟩ : Fin (11 + (u + V.extra))) :=
        Fin.ext rfl
      rw [e, Fin.addCases_left]
      simp

end Assembly

/-! ## One framed request field as a word -/

def fieldFrame (a : DecompositionAlgorithm) (jf : Fin 5) : WordStage a (fun r => RepairOrdinary.frame (fields a r jf)) where
  extra := 13 + 0 + 1
  states := _
  machine := fieldMachineE (e := 0) KeyDecode.FC.machine jf
  cost := fun r => 6 * (r.input a).length + 17 + 1 + (2 * (2 * (fields a r jf).length + 1) + 2)
  coefficient := 30
  degree := 1
  cost_le := by
    intro r
    have h1 := field_le_input a r jf
    have h2 := input_le_small a r
    rw [RepairOrdinary.frame_length] at h1
    rw [pow_one]
    omega
  run := by
    intro r
    have hs := KeyDecode.FC.run (fields a r jf)
    have e1 : (![0, 0] : Fin 2 → ℕ) = fun _ => 0 := by funext i; fin_cases i <;> rfl
    have e2 : (![RepairOrdinary.frame (fields a r jf), []] : Fin 2 → List Bool) =
        scanIn 0 (RepairOrdinary.frame (fields a r jf)) := by
      funext i; fin_cases i <;> rfl
    rw [e1, e2] at hs
    exact field_runW (e := 0) KeyDecode.FC.machine jf a r (RepairOrdinary.frame (fields a r jf)) _ _ _ hs rfl

end
end NearCubicWires.PacketsKeys.Stage

