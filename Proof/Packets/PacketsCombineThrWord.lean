import Proof.Packets.PacketsCoordHoles

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsCombine.Asm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## THR values and the entry bank -/

/-- THR requests. -/
abbrev TReq := FourfoldRequest NormalizedThresholdThresholdCircuit

/-- A THR key-level word. -/
abbrev TVal (a : DecompositionAlgorithm) :=
  ∀ (r : TReq) (_four : r.circuits.length ≤ 4) (L target : ℕ), RCFive.RowKeys.ThrKey a r L target → List Bool

/-- A THR key-level scalar. -/
abbrev TNat (a : DecompositionAlgorithm) :=
  ∀ (r : TReq) (_four : r.circuits.length ≤ 4) (L target : ℕ), RCFive.RowKeys.ThrKey a r L target → ℕ

theorem metaEntry_val (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r)) {t u : ℕ} (i : Fin t)
    (j : Fin u) (h : i.val = j.val) : metaEntry a r c t i = metaEntry a r c u j := by
  unfold metaEntry
  simp only [h]

theorem metaEntry_high (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r)) {t : ℕ} (i : Fin t)
    (h : 9 ≤ i.val) : metaEntry a r c t i = [] := by
  unfold metaEntry
  rw [if_neg (by omega), dif_neg (by omega)]

theorem metaEntry_match (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r)) {t u : ℕ} (i : Fin t)
    (j : Fin u) (h : i.val = j.val ∨ (9 ≤ i.val ∧ 9 ≤ j.val)) : metaEntry a r c t i = metaEntry a r c u j := by
  rcases h with h | ⟨h1, h2⟩
  · exact metaEntry_val a r c i j h
  · rw [metaEntry_high a r c i h1, metaEntry_high a r c j h2]

/-- Cost of two stages in sequence, as one power of `s ≥ 1`. -/
theorem sum_le (s c1 d1 c2 d2 x y : ℕ) (hs : 1 ≤ s) (hx : x ≤ c1 * s ^ d1) (hy : y ≤ c2 * s ^ d2) :
    x + 1 + y ≤ (c1 + 1 + c2) * s ^ (d1 + d2) := by
  have p1 : s ^ d1 ≤ s ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have p2 : s ^ d2 ≤ s ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have p0 : 1 ≤ s ^ (d1 + d2) := Nat.one_le_pow _ _ hs
  have q1 := Nat.mul_le_mul_left c1 p1
  have q2 := Nat.mul_le_mul_left c2 p2
  calc x + 1 + y ≤ c1 * s ^ (d1 + d2) + s ^ (d1 + d2) + c2 * s ^ (d1 + d2) := by omega
    _ = (c1 + 1 + c2) * s ^ (d1 + d2) := by ring

/-! ## The shapes -/

/-- **A THR key-level word** (one fixed machine): from `metaEntry` of a THR request and key (tapes `≥ 9` empty,
heads 0) it writes `v r four L target k` on tape 9 at head 0, keeping tapes 0–8 and their heads. -/
structure ThrWord (a : DecompositionAlgorithm) (v : TVal a) where
  extra : ℕ
  states : ℕ
  machine : Machine (10 + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  run : ∀ (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
    k ∈ RCFive.RowKeys.thrKeys a r L target →
    ∃ (H : Fin (10 + extra) → ℕ) (A : Fin (10 + extra) → List Bool),
      Step machine (cost (.thr r four L target)) (fun _ => 0)
        (metaEntry a (.thr r four L target) (some k) (10 + extra)) H A ∧
      (∀ i : Fin (10 + extra), i.val < 9 →
        A i = metaEntry a (.thr r four L target) (some k) (10 + extra) i ∧ H i = 0) ∧
      A ⟨9, by omega⟩ = v r four L target k ∧ H ⟨9, by omega⟩ = 0

/-- **`n` THR key-level words** on tapes `9..8+n` (one fixed machine), tapes 0–8 kept. -/
structure ThrVec (a : DecompositionAlgorithm) (n : ℕ) (outs : ℕ → TVal a) where
  extra : ℕ
  states : ℕ
  machine : Machine (9 + n + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  run : ∀ (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
    k ∈ RCFive.RowKeys.thrKeys a r L target →
    ∃ (H : Fin (9 + n + extra) → ℕ) (A : Fin (9 + n + extra) → List Bool),
      Step machine (cost (.thr r four L target)) (fun _ => 0)
        (metaEntry a (.thr r four L target) (some k) (9 + n + extra)) H A ∧
      (∀ i : Fin (9 + n + extra), i.val < 9 →
        A i = metaEntry a (.thr r four L target) (some k) (9 + n + extra) i ∧ H i = 0) ∧
      ∀ j (hj : j < n), A ⟨9 + j, by omega⟩ = outs j r four L target k ∧ H ⟨9 + j, by omega⟩ = 0

/-- The input bank of an operation: the words `ins` on tapes `0..m-1`, every other tape empty. -/
def opIn (m t : ℕ) (ins : Fin m → List Bool) (i : Fin t) : List Bool :=
  if h : i.val < m then ins ⟨i.val, h⟩ else []

/-- **An operation** (one fixed machine): from the words `ins x` on tapes `0..m-1` (heads 0, all else empty) it
writes `out x` on tape `m` at head 0, when `pre x`; every other tape existential. -/
structure Op (m : ℕ) (α : Type) (ins : α → Fin m → List Bool) (out : α → List Bool) (pre : α → Prop) where
  extra : ℕ
  states : ℕ
  machine : Machine (m + 1 + extra) states
  cost : α → ℕ
  run : ∀ x, pre x → ∃ (H' : Fin (m + 1 + extra) → ℕ) (A' : Fin (m + 1 + extra) → List Bool),
    Step machine (cost x) (fun _ => 0) (opIn m (m + 1 + extra) (ins x)) H' A' ∧
    A' ⟨m, by omega⟩ = out x ∧ H' ⟨m, by omega⟩ = 0

/-! ## The empty vector and the blank word -/

/-- The machine that halts at once, on `t` tapes. -/
def haltT (t : ℕ) : Machine t 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

theorem haltT_step (t : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool) : Step (haltT t) 0 H A H A :=
  ⟨_, runFrom_zero_of_halted (haltT t) _ rfl, rfl, rfl, le_refl 0⟩

/-- No words. -/
def ThrVec.nil (a : DecompositionAlgorithm) (outs : ℕ → TVal a) : ThrVec a 0 outs where
  extra := 0
  states := 1
  machine := haltT (9 + 0 + 0)
  cost := fun _ => 0
  costC := 0
  costD := 0
  cost_le := fun _ => Nat.zero_le _
  run := fun _ _ _ _ _ _ => ⟨_, _, haltT_step _ _ _, fun _ _ => ⟨rfl, rfl⟩, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- The empty word (tape 9 stays blank). -/
def ThrWord.blank (a : DecompositionAlgorithm) : ThrWord a (fun _ _ _ _ _ => []) where
  extra := 0
  states := 1
  machine := haltT (10 + 0)
  cost := fun _ => 0
  costC := 0
  costD := 0
  cost_le := fun _ => Nat.zero_le _
  run := fun r four L target k _ => ⟨_, _, haltT_step _ _ _, fun _ _ => ⟨rfl, rfl⟩,
    metaEntry_high a (.thr r four L target) (some k) _ (by simp), rfl⟩

/-! ## Appending a word to a vector -/

section Snoc

/-- Slots of the vector so far: tapes below `9 + n` stay, private tapes shift by one. -/
def sA (n eV es : ℕ) (i : Fin (9 + n + eV)) : Fin (9 + (n + 1) + (eV + es)) :=
  ⟨if i.val < 9 + n then i.val else i.val + 1, by have := i.isLt; split_ifs <;> omega⟩

/-- Slots of the new word: key tapes stay, output `9 ↦ 9 + n`, private `10 + i ↦ 10 + n + eV + i`. -/
def sB (n eV es : ℕ) (i : Fin (10 + es)) : Fin (9 + (n + 1) + (eV + es)) :=
  ⟨if i.val < 9 then i.val else if i.val = 9 then 9 + n else i.val + n + eV, by
    have := i.isLt; split_ifs <;> omega⟩

theorem sA_val (n eV es : ℕ) (i : Fin (9 + n + eV)) :
    (sA n eV es i).val = if i.val < 9 + n then i.val else i.val + 1 := rfl

theorem sB_val (n eV es : ℕ) (i : Fin (10 + es)) :
    (sB n eV es i).val = if i.val < 9 then i.val else if i.val = 9 then 9 + n else i.val + n + eV := rfl

theorem sA_inj (n eV es : ℕ) : Function.Injective (sA n eV es) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [sA_val, sA_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem sB_inj (n eV es : ℕ) : Function.Injective (sB n eV es) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [sB_val, sB_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

end Snoc

variable {a : DecompositionAlgorithm}

/-- **Append one word.** -/
def ThrVec.snoc {n : ℕ} {outs : ℕ → TVal a} {w : TVal a} (V : ThrVec a n outs) (s : ThrWord a w) :
    ThrVec a (n + 1) (fun j => if j = n then w else outs j) where
  extra := V.extra + s.extra
  states := _
  machine := Composition.machine (RecoveryFocus.machine (sA n V.extra s.extra) V.machine)
    (RecoveryFocus.machine (sB n V.extra s.extra) s.machine)
  cost := fun r => V.cost r + 1 + s.cost r
  costC := V.costC + 1 + s.costC
  costD := V.costD + s.costD
  cost_le := fun r => sum_le _ _ _ _ _ _ _ (one_le_small a r) (V.cost_le r) (s.cost_le r)
  run := by
    intro r four L target k hk
    obtain ⟨H1, A1, st1, keep1, out1⟩ := V.run r four L target k hk
    obtain ⟨H2, A2, st2, hs2, ho2⟩ := Dock.lift st1 (sA n V.extra s.extra) (sA_inj _ _ _) (fun _ => 0)
      (fun _ => 0) (metaEntry a (.thr r four L target) (some k) (9 + (n + 1) + (V.extra + s.extra))) (by
        intro j
        refine ⟨rfl, ?_⟩
        rw [ZeroPadding.pad_zero]
        apply metaEntry_match
        rw [sA_val]
        split_ifs <;> omega)
    obtain ⟨H3, A3, st3, keep3, out3, hh3⟩ := s.run r four L target k hk
    obtain ⟨H4, A4, st4, hs4, ho4⟩ := Dock.lift st3 (sB n V.extra s.extra) (sB_inj _ _ _) (fun _ => 0) H2 A2 (by
      intro j
      rw [ZeroPadding.pad_zero]
      by_cases hj : j.val < 9
      · have e : sB n V.extra s.extra j = sA n V.extra s.extra ⟨j.val, by omega⟩ :=
          Fin.ext (by simp only [sA_val, sB_val, Fin.val_mk]; split_ifs <;> omega)
        rw [e, (hs2 _).1, (hs2 _).2, ZeroPadding.pad_zero]
        obtain ⟨k1, k2⟩ := keep1 ⟨j.val, by omega⟩ (by simp only [Fin.val_mk]; omega)
        exact ⟨k2, k1.trans (metaEntry_val _ _ _ _ _ rfl)⟩
      · have hn : ∀ i, sA n V.extra s.extra i ≠ sB n V.extra s.extra j := by
          intro i hi
          have hv := congrArg Fin.val hi
          rw [sA_val, sB_val] at hv
          have := i.isLt
          split_ifs at hv <;> omega
        rw [(ho2 _ hn).1, (ho2 _ hn).2]
        refine ⟨rfl, ?_⟩
        rw [metaEntry_high _ _ _ _ (by rw [sB_val]; split_ifs <;> omega), metaEntry_high _ _ _ _ (by omega)])
    refine ⟨_, _, st2.seq st4, ?_, ?_⟩
    · intro i hi
      have e : i = sB n V.extra s.extra ⟨i.val, by omega⟩ :=
        Fin.ext (by simp only [sB_val, Fin.val_mk]; split_ifs <;> omega)
      rw [e, (hs4 _).1, (hs4 _).2, ZeroPadding.pad_zero]
      obtain ⟨k1, k2⟩ := keep3 ⟨i.val, by omega⟩ (by simp only [Fin.val_mk]; omega)
      exact ⟨k1.trans (metaEntry_val _ _ _ _ _ (by simp only [sB_val, Fin.val_mk]; split_ifs <;> omega)), k2⟩
    · intro j hj
      by_cases hjn : j = n
      · have e : (⟨9 + j, by omega⟩ : Fin (9 + (n + 1) + (V.extra + s.extra))) =
            sB n V.extra s.extra ⟨9, by omega⟩ := Fin.ext (by simp only [sB_val, Fin.val_mk]; split_ifs <;> omega)
        rw [e, (hs4 _).1, (hs4 _).2, ZeroPadding.pad_zero, if_pos hjn]
        exact ⟨out3, hh3⟩
      · have hjl : j < n := by omega
        have hn : ∀ i, sB n V.extra s.extra i ≠ ⟨9 + j, by omega⟩ := by
          intro i hi
          have hv := congrArg Fin.val hi
          rw [sB_val] at hv
          simp only [Fin.val_mk] at hv
          have := i.isLt
          split_ifs at hv <;> omega
        have e : (⟨9 + j, by omega⟩ : Fin (9 + (n + 1) + (V.extra + s.extra))) =
            sA n V.extra s.extra ⟨9 + j, by omega⟩ := Fin.ext (by simp only [sA_val, Fin.val_mk]; split_ifs <;> omega)
        rw [(ho4 _ hn).1, (ho4 _ hn).2, e, (hs2 _).1, (hs2 _).2, ZeroPadding.pad_zero, if_neg hjn]
        exact out1 j hjl

/-! ## A vector, then an operation on it, as one word -/

section VecOp

/-- Slots of the vector: key tapes stay, the rest shift by one (tape 9 is the result). -/
def oA (m eV eo : ℕ) (i : Fin (9 + m + eV)) : Fin (10 + (m + eV + eo)) :=
  ⟨if i.val < 9 then i.val else i.val + 1, by have := i.isLt; split_ifs <;> omega⟩

/-- Slots of the operation: inputs `i < m ↦ 10 + i` (the vector's words), output `m ↦ 9`, private tapes last. -/
def oB (m eV eo : ℕ) (i : Fin (m + 1 + eo)) : Fin (10 + (m + eV + eo)) :=
  ⟨if i.val < m then 10 + i.val else if i.val = m then 9 else i.val + 9 + eV, by
    have := i.isLt; split_ifs <;> omega⟩

theorem oA_val (m eV eo : ℕ) (i : Fin (9 + m + eV)) :
    (oA m eV eo i).val = if i.val < 9 then i.val else i.val + 1 := rfl

theorem oB_val (m eV eo : ℕ) (i : Fin (m + 1 + eo)) :
    (oB m eV eo i).val = if i.val < m then 10 + i.val else if i.val = m then 9 else i.val + 9 + eV := rfl

theorem oA_inj (m eV eo : ℕ) : Function.Injective (oA m eV eo) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [oA_val, oA_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem oB_inj (m eV eo : ℕ) : Function.Injective (oB m eV eo) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [oB_val, oB_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

end VecOp

/-- **A vector of words, then one operation on them, as one THR word.** The operation's cost at the key's
values is bounded by `cB · smallSize^dB`, so the word's cost is per request. -/
def ThrWord.ofVecOp {m : ℕ} {outs : ℕ → TVal a} {α : Type} {ins : α → Fin m → List Bool} {out : α → List Bool}
    {pre : α → Prop} (V : ThrVec a m outs) (op : Op m α ins out pre)
    (val : ∀ (r : TReq) (_four : r.circuits.length ≤ 4) (L target : ℕ), RCFive.RowKeys.ThrKey a r L target → α)
    (hin : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target → ∀ i : Fin m,
      outs i.val r four L target k = ins (val r four L target k) i)
    (hpre : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target → pre (val r four L target k))
    (cB dB : ℕ)
    (hB : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target →
      op.cost (val r four L target k) ≤ cB * ((Request.thr r four L target).smallSize a) ^ dB) :
    ThrWord a (fun r four L target k => out (val r four L target k)) where
  extra := m + V.extra + op.extra
  states := _
  machine := Composition.machine (RecoveryFocus.machine (oA m V.extra op.extra) V.machine)
    (RecoveryFocus.machine (oB m V.extra op.extra) op.machine)
  cost := fun r => V.cost r + 1 + cB * (r.smallSize a) ^ dB
  costC := V.costC + 1 + cB
  costD := V.costD + dB
  cost_le := fun r => sum_le _ _ _ _ _ _ _ (one_le_small a r) (V.cost_le r) le_rfl
  run := by
    intro r four L target k hk
    obtain ⟨H1, A1, st1, keep1, out1⟩ := V.run r four L target k hk
    obtain ⟨H2, A2, st2, hs2, ho2⟩ := Dock.lift st1 (oA m V.extra op.extra) (oA_inj _ _ _) (fun _ => 0)
      (fun _ => 0) (metaEntry a (.thr r four L target) (some k) (10 + (m + V.extra + op.extra))) (by
        intro j
        refine ⟨rfl, ?_⟩
        rw [ZeroPadding.pad_zero]
        apply metaEntry_match
        rw [oA_val]
        split_ifs <;> omega)
    obtain ⟨H3, A3, st3, h3A, h3H⟩ := op.run (val r four L target k) (hpre r four L target k hk)
    obtain ⟨H4, A4, st4, hs4, ho4⟩ := Dock.lift st3 (oB m V.extra op.extra) (oB_inj _ _ _) (fun _ => 0) H2 A2 (by
      intro j
      rw [ZeroPadding.pad_zero]
      by_cases hj : j.val < m
      · have e : oB m V.extra op.extra j = oA m V.extra op.extra ⟨9 + j.val, by omega⟩ :=
          Fin.ext (by simp only [oA_val, oB_val, Fin.val_mk]; split_ifs <;> omega)
        rw [e, (hs2 _).1, (hs2 _).2, ZeroPadding.pad_zero]
        obtain ⟨o1, o2⟩ := out1 j.val hj
        refine ⟨o2, ?_⟩
        rw [o1, opIn, dif_pos hj]
        exact hin r four L target k hk ⟨j.val, hj⟩
      · have hn : ∀ i, oA m V.extra op.extra i ≠ oB m V.extra op.extra j := by
          intro i hi
          have hv := congrArg Fin.val hi
          rw [oA_val, oB_val] at hv
          have := i.isLt
          split_ifs at hv <;> omega
        rw [(ho2 _ hn).1, (ho2 _ hn).2]
        refine ⟨rfl, ?_⟩
        rw [metaEntry_high _ _ _ _ (by rw [oB_val]; split_ifs <;> omega), opIn, dif_neg hj])
    have hcost := hB r four L target k hk
    refine ⟨_, _, (st2.seq st4).enlarge (by omega), ?_, ?_, ?_⟩
    · intro i hi
      have hn : ∀ j, oB m V.extra op.extra j ≠ i := by
        intro j hj
        have hv := congrArg Fin.val hj
        rw [oB_val] at hv
        split_ifs at hv <;> omega
      have e : i = oA m V.extra op.extra ⟨i.val, by omega⟩ :=
        Fin.ext (by simp only [oA_val, Fin.val_mk]; split_ifs <;> omega)
      rw [(ho4 _ hn).1, (ho4 _ hn).2, e, (hs2 _).1, (hs2 _).2, ZeroPadding.pad_zero]
      obtain ⟨k1, k2⟩ := keep1 ⟨i.val, by omega⟩ (by simp only [Fin.val_mk]; omega)
      exact ⟨k1.trans (metaEntry_val _ _ _ _ _ (by simp only [oA_val, Fin.val_mk]; split_ifs <;> omega)), k2⟩
    · have e : (⟨9, by omega⟩ : Fin (10 + (m + V.extra + op.extra))) = oB m V.extra op.extra ⟨m, by omega⟩ :=
        Fin.ext (by simp only [oB_val, Fin.val_mk]; split_ifs <;> omega)
      rw [e, (hs4 _).2, ZeroPadding.pad_zero]
      exact h3A
    · have e : (⟨9, by omega⟩ : Fin (10 + (m + V.extra + op.extra))) = oB m V.extra op.extra ⟨m, by omega⟩ :=
        Fin.ext (by simp only [oB_val, Fin.val_mk]; split_ifs <;> omega)
      rw [e, (hs4 _).1]
      exact h3H

/-- A one-argument unary map as an operation. -/
def Op.ofUnaryMap {f : ℕ → ℕ} (M : UnaryMap f) :
    Op 1 ℕ (fun x _ => List.replicate x true) (fun x => List.replicate (f x) true) (fun _ => True) where
  extra := M.extra
  states := M.states
  machine := M.machine
  cost := M.cost
  run := by
    intro x _
    obtain ⟨H', A', st, h1, hh1⟩ := M.run x
    refine ⟨H', A', st.congr_in rfl ?_, h1, hh1⟩
    funext i
    simp only [opIn, unIn]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- A word-valued map as an operation. -/
def Op.ofWordMap {g : ℕ → List Bool} (M : WordMap g) :
    Op 1 ℕ (fun x _ => List.replicate x true) g (fun _ => True) where
  extra := M.extra
  states := M.states
  machine := M.machine
  cost := M.cost
  run := by
    intro x _
    obtain ⟨H', A', st, h1, hh1⟩ := M.run x
    refine ⟨H', A', st.congr_in rfl ?_, h1, hh1⟩
    funext i
    simp only [opIn, unIn]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- A two-argument unary map as an operation. -/
def Op.ofUnaryMap2 {f : ℕ → ℕ → ℕ} (M : UnaryMap2 f) :
    Op 2 (ℕ × ℕ) (fun x i => List.replicate (if i.val = 0 then x.1 else x.2) true)
      (fun x => List.replicate (f x.1 x.2) true) (fun _ => True) where
  extra := M.extra
  states := M.states
  machine := M.machine
  cost := fun x => M.cost x.1 x.2
  run := by
    intro x _
    obtain ⟨H', A', st, h1, hh1⟩ := M.run x.1 x.2
    refine ⟨H', A', st.congr_in rfl ?_, h1, hh1⟩
    funext i
    simp only [opIn, unIn2]
    split_ifs <;> first | rfl | (exfalso; omega)

/-! ## Adapters and derived combinators -/

def ThrWord.ofKeyWord {w : ∀ r : Request, rcKey a r → List Bool} (s : Residual.KeyWord a w) (v : TVal a)
    (hv : ∀ r four L target (k : RCFive.RowKeys.ThrKey a r L target), w (.thr r four L target) k = v r four L target k) :
    ThrWord a v where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  costC := s.costC
  costD := s.costD
  cost_le := s.cost_le
  run := by
    intro r four L target k hk
    obtain ⟨H, A, st, keep, h9, hh9⟩ := s.run (.thr r four L target) k hk
    exact ⟨H, A, st, keep, h9.trans (hv r four L target k), hh9⟩

def ThrWord.ofWord {w : Request → List Bool} (s : WordStage a w) :
    ThrWord a (fun r four L target _ => w (.thr r four L target)) :=
  ThrWord.ofKeyWord (Residual.KeyWord.ofWord s) _ (fun _ _ _ _ _ => rfl)

def ThrWord.ofUnary {v : Request → ℕ} (s : UnaryStage a v) :
    ThrWord a (fun r four L target _ => List.replicate (v (.thr r four L target)) true) :=
  ThrWord.ofWord s.toWord

/-- **A word followed by a unary map.** -/
def ThrWord.thenMap {u : TNat a} {f : ℕ → ℕ}
    (s : ThrWord a (fun r four L target k => List.replicate (u r four L target k) true)) (M : UnaryMap f)
    (cB dB : ℕ) (hB : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target →
      M.cost (u r four L target k) ≤ cB * ((Request.thr r four L target).smallSize a) ^ dB) :
    ThrWord a (fun r four L target k => List.replicate (f (u r four L target k)) true) :=
  ThrWord.ofVecOp ((ThrVec.nil a (fun _ _ _ _ _ _ => [])).snoc s) (Op.ofUnaryMap M) u
    (fun r four L target k _ i => by
      have hi : i.val = 0 := by omega
      simp only [hi, if_pos])
    (fun _ _ _ _ _ _ => trivial) cB dB hB

/-- **A word followed by a word-valued map.** -/
def ThrWord.thenWord {u : TNat a} {g : ℕ → List Bool}
    (s : ThrWord a (fun r four L target k => List.replicate (u r four L target k) true)) (M : WordMap g)
    (cB dB : ℕ) (hB : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target →
      M.cost (u r four L target k) ≤ cB * ((Request.thr r four L target).smallSize a) ^ dB) :
    ThrWord a (fun r four L target k => g (u r four L target k)) :=
  ThrWord.ofVecOp ((ThrVec.nil a (fun _ _ _ _ _ _ => [])).snoc s) (Op.ofWordMap M) u
    (fun r four L target k _ i => by
      have hi : i.val = 0 := by omega
      simp only [hi, if_pos])
    (fun _ _ _ _ _ _ => trivial) cB dB hB

/-- **Two words followed by a two-argument unary map.** -/
def ThrWord.pair {u1 u2 : TNat a} {f : ℕ → ℕ → ℕ}
    (s1 : ThrWord a (fun r four L target k => List.replicate (u1 r four L target k) true))
    (s2 : ThrWord a (fun r four L target k => List.replicate (u2 r four L target k) true)) (M : UnaryMap2 f)
    (cB dB : ℕ) (hB : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target →
      M.cost (u1 r four L target k) (u2 r four L target k) ≤ cB * ((Request.thr r four L target).smallSize a) ^ dB) :
    ThrWord a (fun r four L target k => List.replicate (f (u1 r four L target k) (u2 r four L target k)) true) :=
  ThrWord.ofVecOp (((ThrVec.nil a (fun _ _ _ _ _ _ => [])).snoc s1).snoc s2) (Op.ofUnaryMap2 M)
    (fun r four L target k => (u1 r four L target k, u2 r four L target k))
    (fun r four L target k _ i => by
      rcases i with ⟨i, hi⟩
      rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> subst h <;> simp)
    (fun _ _ _ _ _ _ => trivial) cB dB hB

end
end NearCubicWires.PacketsCombine.Asm

