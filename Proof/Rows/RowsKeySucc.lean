import Proof.Rows.RowsKeyStep
import Proof.Packets.PacketsCursorOrder

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeySucc
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc
open RowsConstruction.BaseLayout
noncomputable section

/-! ## 1. The compiled census of the THR traversal input -/

/-- The ports where the THR traversal input depends on the row key or the cell. -/
def thrKeyPorts : Finset (Fin 254) := {109, 149, 209, 218, 220, 228, 229, 230, 231, 240, 242}

section Census
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (I : Finset (Fin r.q)) (T L target w F U v : Nat)

set_option linter.unnecessarySeqFocus false in
/-- **Off the key ports the input does not depend on the key or the cell.** -/
theorem thr_other (sel sel' : ThresholdRows.Selection a r) (x x' : BitInput r.q) {cutoff : Nat}
    (prime prime' : PrimeIndex cutoff) (o : Fin prime.val) (o' : Fin prime'.val) (i : Fin 254)
    (hi : i ∉ thrKeyPorts) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v i =
      PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel' I x' prime' o' T L target w F U v i := by
  fin_cases i <;> first
    | exact absurd (by decide) hi
    | (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input <;>
        bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input <;> rfl)

variable (sel : ThresholdRows.Selection a r) (x : BitInput r.q) {cutoff : Nat} (prime : PrimeIndex cutoff)
  (o : Fin prime.val)

theorem thr_242 : PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v 242 =
    frame (SignedSortKey.binary w o.val) := by
  bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input
  rfl

theorem pad_zero (l : List Bool) : ZeroPadding.pad 0 l = l := by
  simp [ZeroPadding.pad]

theorem thr_prime_ports (i : Fin 254) (hi : i = 149 ∨ i = 218 ∨ i = 240) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v i =
      frame (SignedSortKey.binary w prime.val) := by
  rcases hi with rfl | rfl | rfl <;>
    (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input; simp only [pad_zero])

theorem thr_209 : PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v 209 =
    ZeroPadding.pad F (frame (SignedSortKey.binary w prime.val)) := by
  bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input
  simp only [pad_zero]

theorem thr_220 : PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v 220 =
    ZeroPadding.pad U (frame (SignedSortKey.binary w (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel))) := by
  bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input
  simp only [pad_zero]

theorem thr_digit_ports (c : Fin 4) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v
      ⟨228+c.val, by omega⟩ =
      frame (SignedSortKey.binary v ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).digits c)) := by
  fin_cases c <;> (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input; rfl)

end Census

theorem next_append_of_some {ι : Type} [DecidableEq ι] : ∀ (ls1 ls2 : List (Level ι)) (d e : ι → ℕ),
    next ls2 d = some e → next (ls1 ++ ls2) d = some e
  | [], _, _, _, h => h
  | l :: ls1, ls2, d, e, h => next_cons_of_some l (ls1 ++ ls2) d e (next_append_of_some ls1 ls2 d e h)

section Succ
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

abbrev keys := RCFive.RowKeys.thrKeys a r L target
abbrev dig := thrDigitsOf a r L target
abbrev spec := cursorSpec a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target)
abbrev cut := CloseoutFinalC10ThresholdRows.primeCutoff a r target

/-- Consecutive keys: the carry cascade maps `keys[j]`'s digits to `keys[j+1]`'s. -/
theorem thr_next (j : Nat) (hj : j+1 < (keys a r L target).length) :
    next (spec a r four L target) (dig a r L target (keys a r L target)[j]) =
      some (dig a r L target (keys a r L target)[j+1]) := by
  have hne : PacketFamilyParent.rcKeys a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target) ≠ [] := by
    change keys a r L target ≠ []
    intro h
    rw [h] at hj
    simp at hj
  have hc := (enum_next (spec a r four L target) (cursorSpec_wf a _) (cursorSpec_pos a _ hne) (fun _ => 0)).1
  rw [← thr_digits a r four L target] at hc
  have h := hc.getElem j (by rw [List.length_map]; exact hj)
  simpa only [List.getElem_map] using h

include four in
theorem dig_res (k : RCFive.RowKeys.ThrKey a r L target) : dig a r L target k 6 = k.residue.val := by
  have h : ¬ ((6 : Fin 8).val < r.circuits.length) := by simp; omega
  unfold dig thrDigitsOf
  rw [dif_neg h]
  rfl

include four in
theorem dig_seed (k : RCFive.RowKeys.ThrKey a r L target) :
    dig a r L target k 5 = thrSeedIdx a r L target k := by
  have h : ¬ ((5 : Fin 8).val < r.circuits.length) := by simp; omega
  unfold dig thrDigitsOf thrSeedIdx
  rw [dif_neg h]
  rfl

include four in
theorem dig_prime (k : RCFive.RowKeys.ThrKey a r L target) :
    dig a r L target k 4 = (primeIndexFinEquiv (cut a r target) k.prime).val := by
  have h : ¬ ((4 : Fin 8).val < r.circuits.length) := by simp; omega
  unfold dig thrDigitsOf
  rw [dif_neg h]
  rfl

include four in
theorem primeAt_dig (k : RCFive.RowKeys.ThrKey a r L target) :
    primeAt (cut a r target) (dig a r L target k 4) = k.prime.val := by
  rw [dig_prime a r four L target k]
  unfold primeAt
  rw [dif_pos (Fin.isLt _)]
  simp

include four in
theorem dig_sel (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin r.circuits.length) :
    dig a r L target k ⟨i.val, by omega⟩ = (k.selection i).val := by
  unfold dig thrDigitsOf
  rw [dif_pos i.isLt]

def Rl : Level (Fin 8) := ⟨6, fun d => primeAt (cut a r target) (d 4)⟩
def Sl : Level (Fin 8) := ⟨5, fun _ => (thrSeeds a r L target).length⟩
def Pl : Level (Fin 8) := ⟨4, fun _ => Fintype.card (PrimeIndex (cut a r target))⟩
include four in
def coords : List (Level (Fin 8)) :=
  coordLevels 0 r.circuits.length (by omega) (fun i => (ThresholdRows.children a (r.circuits.get i)).length)

theorem spec_eq : spec a r four L target =
    coords a r four ++ [Pl a r target, Sl a r L target, Rl a r target] := rfl

include four in
/-- **Case R**: the residue advances. -/
theorem thr_caseR (j : Nat) (hj : j+1 < (keys a r L target).length)
    (h : (keys a r L target)[j].residue.val + 1 < (keys a r L target)[j].prime.val) :
    dig a r L target (keys a r L target)[j+1] =
      Function.update (dig a r L target (keys a r L target)[j]) 6 ((keys a r L target)[j].residue.val + 1) := by
  have hn := thr_next a r four L target j hj
  have hb : dig a r L target (keys a r L target)[j] 6 + 1 <
      primeAt (cut a r target) (dig a r L target (keys a r L target)[j] 4) := by
    rw [dig_res a r four, primeAt_dig a r four]; exact h
  have hR : next [Rl a r target] (dig a r L target (keys a r L target)[j]) =
      some (Function.update (dig a r L target (keys a r L target)[j]) 6
        ((keys a r L target)[j].residue.val + 1)) := by
    rw [next_cons_of_none _ _ _ rfl]
    simp only [Rl, zero]
    rw [if_pos hb, dig_res a r four]
  have e := next_append_of_some (coords a r four ++ [Pl a r target, Sl a r L target]) [Rl a r target] _ _ hR
  rw [List.append_assoc] at e
  change next (spec a r four L target) _ = _ at e
  rw [hn] at e
  exact Option.some.inj e

include four in
/-- **Case S**: the residue wraps, the seed advances. -/
theorem thr_caseS (j : Nat) (hj : j+1 < (keys a r L target).length)
    (h1 : ¬ (keys a r L target)[j].residue.val + 1 < (keys a r L target)[j].prime.val)
    (h2 : thrSeedIdx a r L target (keys a r L target)[j] + 1 < (thrSeeds a r L target).length) :
    dig a r L target (keys a r L target)[j+1] =
      Function.update (Function.update (dig a r L target (keys a r L target)[j]) 5
        (thrSeedIdx a r L target (keys a r L target)[j] + 1)) 6 0 := by
  have hn := thr_next a r four L target j hj
  have hb : ¬ dig a r L target (keys a r L target)[j] 6 + 1 <
      primeAt (cut a r target) (dig a r L target (keys a r L target)[j] 4) := by
    rw [dig_res a r four, primeAt_dig a r four]; exact h1
  have hR : next [Rl a r target] (dig a r L target (keys a r L target)[j]) = none := by
    rw [next_cons_of_none _ _ _ rfl]
    simp only [Rl]
    rw [if_neg hb]
  have hS : next [Sl a r L target, Rl a r target] (dig a r L target (keys a r L target)[j]) =
      some (Function.update (Function.update (dig a r L target (keys a r L target)[j]) 5
        (thrSeedIdx a r L target (keys a r L target)[j] + 1)) 6 0) := by
    rw [next_cons_of_none _ _ _ hR]
    simp only [Sl, Rl, zero]
    rw [if_pos (by rw [dig_seed a r four]; exact h2), dig_seed a r four]
  have e := next_append_of_some (coords a r four ++ [Pl a r target]) [Sl a r L target, Rl a r target] _ _ hS
  rw [List.append_assoc] at e
  change next (spec a r four L target) _ = _ at e
  rw [hn] at e
  exact Option.some.inj e

set_option linter.unnecessarySeqFocus false in
/-- Two keys with the same selection and prime give the same traversal input off port 242. -/
theorem input_off242 (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q)) (x : BitInput r.q)
    {cutoff : Nat} (prime : PrimeIndex cutoff) (o o' : Fin prime.val) (T w F U v : Nat) (i : Fin 254)
    (hi : i ≠ 242) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v i =
      PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o' T L target w F U v i := by
  by_cases hk : i ∈ thrKeyPorts
  · simp only [thrKeyPorts, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hi
      | (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input <;>
          bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input <;> rfl)
  · exact thr_other a r four I T L target w F U v sel sel x x prime prime o o' i hk

/-- **Masters of two keys with the same selection and prime differ only at the residue port 242.** -/
theorem masters_same (R : Nat) (k k' : RCFive.RowKeys.ThrKey a r L target) (hs : k'.selection = k.selection)
    (hp : k'.prime = k.prime) :
    thrMasters a r four L target R k' =
      Function.update (thrMasters a r four L target R k) 242
        (frame (SignedSortKey.binary (12*ThrWidth.T a r four L target+19) k'.residue.val)) := by
  obtain ⟨s, p, e, o⟩ := k
  obtain ⟨s', p', e', o'⟩ := k'
  simp only at hs hp
  subst hs hp
  funext i
  by_cases hi : i = 242
  · subst hi
    rw [Function.update_self]
    unfold thrMasters
    rw [if_neg (by decide), keyPad_key _ (by decide)]
    exact thr_242 a r four _ _ L target _ _ _ _ _ _ _ _
  · rw [Function.update_of_ne hi]
    unfold thrMasters
    split
    · rfl
    · exact congrArg (keyPad thrKeySet R i) (input_off242 a r four L target _ _ _ _ _ _ _ _ _ _ _ _ hi)

include four in
theorem sel_of_dig (k k' : RCFive.RowKeys.ThrKey a r L target)
    (h : ∀ c : Fin r.circuits.length, dig a r L target k' ⟨c.val, by omega⟩ = dig a r L target k ⟨c.val, by omega⟩) :
    k'.selection = k.selection := by
  funext c
  apply Fin.ext
  have hc := h c
  rwa [dig_sel a r four L target k' c, dig_sel a r four L target k c] at hc

include four in
theorem prime_of_dig (k k' : RCFive.RowKeys.ThrKey a r L target)
    (h : dig a r L target k' 4 = dig a r L target k 4) : k'.prime = k.prime := by
  rw [dig_prime a r four L target k', dig_prime a r four L target k] at h
  exact (primeIndexFinEquiv (cut a r target)).injective (Fin.ext h)

include four in
/-- **Case R at key level.** -/
theorem thr_keyR (j : Nat) (hj : j+1 < (keys a r L target).length)
    (h : (keys a r L target)[j].residue.val + 1 < (keys a r L target)[j].prime.val) :
    (keys a r L target)[j+1].selection = (keys a r L target)[j].selection ∧
    (keys a r L target)[j+1].prime = (keys a r L target)[j].prime ∧
    thrSeedIdx a r L target (keys a r L target)[j+1] = thrSeedIdx a r L target (keys a r L target)[j] ∧
    (keys a r L target)[j+1].residue.val = (keys a r L target)[j].residue.val + 1 := by
  have hd := thr_caseR a r four L target j hj h
  refine ⟨sel_of_dig a r four L target _ _ (fun c => ?_), prime_of_dig a r four L target _ _ ?_, ?_, ?_⟩
  · rw [hd, Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]
  · rw [hd, Function.update_of_ne (by decide)]
  · rw [← dig_seed a r four, ← dig_seed a r four, hd, Function.update_of_ne (by decide)]
  · rw [← dig_res a r four, hd, Function.update_self]

include four in
/-- **Case S at key level.** -/
theorem thr_keyS (j : Nat) (hj : j+1 < (keys a r L target).length)
    (h1 : ¬ (keys a r L target)[j].residue.val + 1 < (keys a r L target)[j].prime.val)
    (h2 : thrSeedIdx a r L target (keys a r L target)[j] + 1 < (thrSeeds a r L target).length) :
    (keys a r L target)[j+1].selection = (keys a r L target)[j].selection ∧
    (keys a r L target)[j+1].prime = (keys a r L target)[j].prime ∧
    thrSeedIdx a r L target (keys a r L target)[j+1] = thrSeedIdx a r L target (keys a r L target)[j] + 1 ∧
    (keys a r L target)[j+1].residue.val = 0 := by
  have hd := thr_caseS a r four L target j hj h1 h2
  refine ⟨sel_of_dig a r four L target _ _ (fun c => ?_), prime_of_dig a r four L target _ _ ?_, ?_, ?_⟩
  · rw [hd, Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]
  · rw [hd, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · rw [← dig_seed a r four, hd, Function.update_of_ne (by decide), Function.update_self]
  · rw [← dig_res a r four, hd, Function.update_self]

end Succ

end
end RowsConstruction.KeySucc
