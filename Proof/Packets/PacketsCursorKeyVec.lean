import Proof.Packets.PacketsMetaKeyWords
import Proof.Packets.PacketsCursorChain

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Cursor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsMeta.Keys
open NearCubicWires.PacketsGlue.CursorKit
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## Key-level word vectors -/

/-- **`n` key-level words, one fixed machine**: from `metaEntry` (tapes `≥ 9` empty, heads 0), `outs j r k` on tape
`9 + j` at head 0, tapes 0–8 kept with heads 0; private tapes existential. -/
structure KeyVec (a : DecompositionAlgorithm) (n : ℕ) (outs : ℕ → ∀ r : Request, rcKey a r → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (9 + n + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  run : ∀ r (k : rcKey a r), k ∈ rcKeys a r →
    ∃ (H : Fin (9 + n + extra) → ℕ) (A : Fin (9 + n + extra) → List Bool),
      Step machine (cost r) (fun _ => 0) (PacketsCombine.metaEntry a r (some k) (9 + n + extra)) H A ∧
      (∀ i : Fin (9 + n + extra), i.val < 9 →
        A i = PacketsCombine.metaEntry a r (some k) (9 + n + extra) i ∧ H i = 0) ∧
      (∀ j (hj : j < n), A ⟨9 + j, by omega⟩ = outs j r k ∧ H ⟨9 + j, by omega⟩ = 0)

/-- The machine that halts at once, on nine tapes. -/
def halt9 : Machine (9 + 0 + 0) 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

/-- No words. -/
def KeyVec.nil (a : DecompositionAlgorithm) (outs : ℕ → ∀ r : Request, rcKey a r → List Bool) : KeyVec a 0 outs where
  extra := 0
  states := 1
  machine := halt9
  cost := fun _ => 0
  costC := 0
  costD := 0
  cost_le := fun _ => Nat.zero_le _
  run := fun r k _ => ⟨fun _ => 0, PacketsCombine.metaEntry a r (some k) (9 + 0 + 0),
    ⟨_, runFrom_zero_of_halted halt9 _ rfl, rfl, rfl, le_refl 0⟩, fun _ _ => ⟨rfl, rfl⟩,
    fun j hj => absurd hj (Nat.not_lt_zero j)⟩

section Snoc
variable (n eV es : ℕ)

/-- The vector so far: tapes below `9 + n` in place, private tapes one up. -/
def kvA (j : Fin (9 + n + eV)) : Fin (9 + (n + 1) + (eV + es)) :=
  ⟨if j.val < 9 + n then j.val else j.val + 1, by have := j.isLt; split_ifs <;> omega⟩

/-- The new word: tapes 0–8 in place, output `9 + n`, private tapes after the vector's. -/
def kvB (j : Fin (10 + es)) : Fin (9 + (n + 1) + (eV + es)) :=
  ⟨if j.val < 9 then j.val else if j.val = 9 then 9 + n else j.val + n + eV, by
    have := j.isLt; split_ifs <;> omega⟩

theorem kvA_val (j : Fin (9 + n + eV)) : (kvA n eV es j).val = if j.val < 9 + n then j.val else j.val + 1 := rfl
theorem kvB_val (j : Fin (10 + es)) :
    (kvB n eV es j).val = if j.val < 9 then j.val else if j.val = 9 then 9 + n else j.val + n + eV := rfl

theorem kvA_inj : Function.Injective (kvA n eV es) := by
  intro x y h; have hv := congrArg Fin.val h; rw [kvA_val, kvA_val] at hv; apply Fin.ext; split_ifs at hv <;> omega

theorem kvB_inj : Function.Injective (kvB n eV es) := by
  intro x y h; have hv := congrArg Fin.val h; rw [kvB_val, kvB_val] at hv; apply Fin.ext; split_ifs at hv <;> omega

theorem kvB_notA (j : Fin (10 + es)) (hj : 9 ≤ j.val) (i : Fin (9 + n + eV)) : kvA n eV es i ≠ kvB n eV es j := by
  intro h; have hv := congrArg Fin.val h; rw [kvA_val, kvB_val] at hv; have := i.isLt; split_ifs at hv <;> omega

end Snoc

theorem kv_cost_kb {n : ℕ} {outs : ℕ → ∀ r : Request, rcKey a r → List Bool} {w : ∀ r : Request, rcKey a r → List Bool}
    (V : KeyVec a n outs) (s : KeyWord a w) : KB a (fun r => V.cost r + 1 + s.cost r) :=
  KB.add (KB.add ⟨V.costC, V.costD, V.cost_le⟩ (KB.const 1) (fun _ => le_refl _)) (KB.cost s) (fun _ => le_refl _)

/-- **Append one key-level word.** -/
def KeyVec.snoc {n : ℕ} {outs : ℕ → ∀ r : Request, rcKey a r → List Bool} {w : ∀ r : Request, rcKey a r → List Bool}
    (V : KeyVec a n outs) (s : KeyWord a w) : KeyVec a (n + 1) (fun j => if j = n then w else outs j) where
  extra := V.extra + s.extra
  states := _
  machine := Composition.machine (RecoveryFocus.machine (kvA n V.extra s.extra) V.machine)
    (RecoveryFocus.machine (kvB n V.extra s.extra) s.machine)
  cost := fun r => V.cost r + 1 + s.cost r
  costC := (kv_cost_kb V s).c
  costD := (kv_cost_kb V s).d
  cost_le := (kv_cost_kb V s).spec
  run := fun r k hk => by
    refine (V.run r k hk).elim fun H1 e1 => e1.elim fun A1 f1 => ?_
    have st1 := f1.1
    have keep1 := f1.2.1
    have out1 := f1.2.2
    refine (Dock.lift st1 (kvA n V.extra s.extra) (kvA_inj _ _ _) (fun _ => 0) (fun _ => 0)
      (PacketsCombine.metaEntry a r (some k) (9 + (n + 1) + (V.extra + s.extra))) (fun j => by
        refine ⟨rfl, ?_⟩
        rw [ZeroPadding.pad_zero]
        by_cases h9 : j.val < 9
        · exact me_congr r (some k) _ _ (by rw [kvA_val, if_pos (by omega)])
        · rw [me_hi r (some k) _ (by rw [kvA_val]; split_ifs <;> omega), me_hi r (some k) _ (by omega)])).elim
      fun H2 e2 => e2.elim fun A2 f2 => ?_
    have st2 := f2.1
    have sl2 := f2.2.1
    have ot2 := f2.2.2
    have nA : ∀ j : Fin (10 + s.extra), 9 ≤ j.val → ∀ i, kvA n V.extra s.extra i ≠ kvB n V.extra s.extra j :=
      fun j hj i => kvB_notA n V.extra s.extra j hj i
    refine (kw_dock s (kvB n V.extra s.extra) (kvB_inj _ _ _) r k hk H2 A2 (fun j => by
        by_cases h9 : j.val < 9
        · have e : kvB n V.extra s.extra j = kvA n V.extra s.extra ⟨j.val, by omega⟩ :=
            Fin.ext (by simp only [kvA_val, kvB_val]; split_ifs <;> omega)
          rw [e, (sl2 _).1, (sl2 _).2, ZeroPadding.pad_zero, (keep1 _ h9).1, (keep1 _ h9).2]
          exact ⟨rfl, me_congr r (some k) _ _ rfl⟩
        · have ho := ot2 _ (fun i => nA j (by omega) i)
          rw [ho.1, ho.2, me_hi r (some k) _ (by rw [kvB_val]; split_ifs <;> omega), me_hi r (some k) _ (by omega)]
          exact ⟨rfl, rfl⟩)).elim fun H3 e3 => e3.elim fun A3 f3 => ?_
    have st3 := f3.1
    have lo3 := f3.2.1
    have h93 := f3.2.2.1
    have a93 := f3.2.2.2.1
    have ot3 := f3.2.2.2.2
    refine ⟨H3, A3, st2.seq st3, fun i hi => ?_, fun j hj => ?_⟩
    · have e : i = kvB n V.extra s.extra ⟨i.val, by omega⟩ := Fin.ext (by rw [kvB_val, if_pos hi])
      rw [e, (lo3 _ hi).1, (lo3 _ hi).2]
      exact ⟨me_congr r (some k) _ _ (by simp only [kvB_val]; split_ifs; omega), rfl⟩
    · by_cases hjn : j = n
      · subst hjn
        have e : (⟨9 + j, by omega⟩ : Fin (9 + (j + 1) + (V.extra + s.extra))) = kvB j V.extra s.extra ⟨9, by omega⟩ :=
          Fin.ext (by rw [kvB_val]; simp)
        rw [if_pos rfl, e, a93, h93]
        exact ⟨rfl, rfl⟩
      · have hjl : j < n := by omega
        simp only [if_neg hjn]
        have e : (⟨9 + j, by omega⟩ : Fin (9 + (n + 1) + (V.extra + s.extra))) =
            kvA n V.extra s.extra ⟨9 + j, by omega⟩ := Fin.ext (by simp only [kvA_val]; split_ifs <;> omega)
        have hn : ∀ l, kvB n V.extra s.extra l ≠ kvA n V.extra s.extra ⟨9 + j, by omega⟩ := by
          intro l hl
          have hv := congrArg Fin.val hl
          simp only [kvA_val, kvB_val] at hv
          have := l.isLt
          split_ifs at hv <;> omega
        rw [e, (ot3 _ hn).1, (ot3 _ hn).2, (sl2 _).1, (sl2 _).2, ZeroPadding.pad_zero]
        exact ⟨(out1 j hjl).1, (out1 j hjl).2⟩

/-! ## The carry flag as a two-argument unary map -/

def cS1 : Fin 3 → Fin 6 := ![1, 3, 4]
def cS2 : Fin 4 → Fin 6 := ![0, 3, 2, 5]

theorem cS1_inj : Function.Injective cS1 := by decide
theorem cS2_inj : Function.Injective cS2 := by decide

/-- Template of `d` (tape 1 → 3), then the masked comparator against `1^b` (tape 0), flag on tape 2. -/
def carryMachine :=
  Composition.machine
    (RecoveryFocus.machine cS1 (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
    (RecoveryFocus.machine cS2 (MaskedReset.machine Carry.machine (fun _ => true)))

theorem carry_step (b d : ℕ) : ∃ A' : Fin 6 → List Bool,
    Step carryMachine (2 * d + 8 + 1 + (2 * (b + 3) + 2)) (fun _ => 0) (unIn2 6 b d) (fun _ => 0) A' ∧
      A' 2 = List.replicate (carryV b d) true := by
  have d1 := (PacketsGlue.RequestMeta.tpl_step d).dock cS1 cS1_inj (fun _ => 0) (unIn2 6 b d) (fun _ => rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [dockH_zero] at d1
  set A1 := install cS1 (unIn2 6 b d)
    ![List.replicate d true, UnaryTemplate.tape d, List.replicate (d + 3) false] with hA1
  have a0 : A1 0 = List.replicate b true := by rw [hA1, install_other _ _ _ _ (by decide)]; rfl
  have a3 : A1 3 = UnaryTemplate.tape d := by
    rw [hA1, show (3 : Fin 6) = cS1 1 from rfl, install_slot _ cS1_inj]; rfl
  have a2 : A1 2 = [] := by rw [hA1, install_other _ _ _ _ (by decide)]; rfl
  have a5 : A1 5 = [] := by rw [hA1, install_other _ _ _ _ (by decide)]; rfl
  obtain ⟨kk, hc⟩ := carry_local b d
  have d2 := hc.dock cS2 cS2_inj (fun _ => 0) A1 (fun _ => rfl)
    (by
      intro j; fin_cases j
      · exact a0
      · exact a3
      · exact a2
      · exact a5)
  rw [dockH_zero] at d2
  refine ⟨_, d1.seq d2, ?_⟩
  rw [show (2 : Fin 6) = cS2 2 from rfl, install_slot _ cS2_inj]
  rfl

/-- **The carry flag** `[b ≤ d + 1]` as a unary map of `(b, d)`. -/
def carryMap2 : UnaryMap2 (fun b d => carryV b d) where
  extra := 3
  states := _
  machine := carryMachine
  cost := fun b d => 2 * d + 8 + 1 + (2 * (b + 3) + 2)
  run := by
    intro b d
    obtain ⟨A', h, h2⟩ := carry_step b d
    exact ⟨fun _ => 0, A', h, h2, rfl⟩

/-! ## The carry flag of one key field, as a key word -/

section Flag

def flagMb (a : DecompositionAlgorithm) (B : Request → ℕ) (r : Request) : ℕ := 2 * (B r + digitBound a r) + 17

theorem flagMb_le {v1 : ∀ r : Request, rcKey a r → ℕ} (f : Fin 8) (B : Request → ℕ)
    (hB : ∀ r k, k ∈ rcKeys a r → v1 r k ≤ B r) (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) :
    carryMap2.cost (v1 r k) (keyDigits a r (some k) f) ≤ flagMb a B r := by
  have h1 := hB r k hk
  have h2 := digit_lt_bound a r (some k) (Or.inr ⟨k, hk, rfl⟩) f
  change 2 * keyDigits a r (some k) f + 8 + 1 + (2 * (v1 r k + 3) + 2) ≤ 2 * (B r + digitBound a r) + 17
  omega

theorem flagMb_kb (B : Request → ℕ) (hBk : KB a B) : KB a (flagMb a B) :=
  KB.add (KB.mul (KB.const 2) (KB.add hBk (digit_kb a) (fun _ => le_refl _)) (fun _ => le_refl _)) (KB.const 17)
    (fun _ => le_refl _)

/-- **The carry flag of key field `f`** against the bound word `s1`: `[v1 ≤ digit f + 1]` as `1^carryV`. -/
def flagKW {v1 : ∀ r : Request, rcKey a r → ℕ} (s1 : KeyWord a (fun r k => List.replicate (v1 r k) true))
    (f : Fin 8) (B : Request → ℕ) (hB : ∀ r k, k ∈ rcKeys a r → v1 r k ≤ B r) (hBk : KB a B) :
    KeyWord a (fun r k => List.replicate (carryV (v1 r k) (keyDigits a r (some k) f)) true) :=
  KeyWord.pair (v2 := fun r k => keyDigits a r (some k) f) s1 (fieldKey a f) carryMap2 (flagMb a B)
    (flagMb_le f B hB) (flagMb_kb B hBk)

end Flag

theorem carryV_read (b d : ℕ) : readTapeBit (List.replicate (carryV b d) true) 0 = decide (b ≤ d + 1) := by
  unfold carryV
  split_ifs with h
  · simp [h, readTapeBit]
  · simp [h, readTapeBit]

end
end NearCubicWires.PacketsConstruction.Cursor
