import Proof.SourceAssembly.SourceFactorSelDesc
import Proof.SourceAssembly.SourceRequestSymSwitch

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Modes
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierPipeline SourceInterfaces
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest
open PCJ6e421fabe2aa4155_SourceSymmetricMeaning (bitmap)
open Desc (Kind gdesc)
noncomputable section

section
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- A slot's kind in the branch mode (`false` THR, `true` SYM); an atom of the other mode is not admitted
(`ThrSwitch.ok` / `SymSwitch.ok` are `False` there) and gets no descriptor. -/
def kindOf (mode : Bool) : Option (C10TotalDecode.Atom pcpp) → Kind
  | none => .absent
  | some (.systematic _) => .sys
  | some (.threshold _) => if mode then .absent else .orig
  | some (.symmetric _) => if mode then .orig else .absent

/-- A systematic slot's support bitmap. -/
def bmOf : Option (C10TotalDecode.Atom pcpp) → List Bool
  | some (.systematic idx) => bitmap (pcpp.systematicSupport idx)
  | _ => []

def bitsOf (mode : Bool) (L : Nat) : Option (C10TotalDecode.Atom pcpp) → List Bool
  | some (.threshold c) => if mode then [] else ThrSwitch.codeBits L c
  | some (.symmetric c) => if mode then SymOriginal.symCodeBits L c else []
  | _ => []

theorem thr_descAt (P W L : Nat) (o : Option (C10TotalDecode.Atom pcpp)) (n : Nat) :
    ThrSwitch.descAt P W L o n = gdesc (UnaryTemplate.tape q) (List.replicate P true)
      (List.replicate W true) (List.replicate L true) (bmOf o) (bitsOf false L o) (kindOf false o) n := by
  rcases o with _ | (idx | c | c)
  · rfl
  · by_cases hn : n < 16
    · interval_cases n <;> simp [ThrSwitch.descAt, ThrSwitch.sysDescAt, gdesc, kindOf, bmOf]
    · simp [ThrSwitch.descAt, gdesc, kindOf, show ¬ n < 4 by omega, show n ≠ 14 by omega,
        show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
  · rfl
  · by_cases hn : n < 16
    · interval_cases n <;> simp [ThrSwitch.descAt, ThrSwitch.origDescAt, ThrOriginal.thrAt,
        ThrOriginal.posVal, gdesc, kindOf, bitsOf]
    · simp [ThrSwitch.descAt, gdesc, kindOf, show ¬ n < 4 by omega, show ¬ n < 14 by omega,
        show n ≠ 15 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
        show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
        show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega]

theorem sym_descAt (P W L : Nat) (o : Option (C10TotalDecode.Atom pcpp)) (n : Nat) :
    SymSwitch.descAt P W L o n = gdesc (UnaryTemplate.tape q) (List.replicate P true)
      (List.replicate W true) (List.replicate L true) (bmOf o) (bitsOf true L o) (kindOf true o) n := by
  rcases o with _ | (idx | c | c)
  · rfl
  · by_cases hn : n < 16
    · interval_cases n <;> simp [SymSwitch.descAt, ThrSwitch.sysDescAt, gdesc, kindOf, bmOf]
    · simp [SymSwitch.descAt, gdesc, kindOf, show ¬ n < 4 by omega, show n ≠ 14 by omega,
        show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
  · by_cases hn : n < 16
    · interval_cases n <;> simp [SymSwitch.descAt, ThrSwitch.origDescAt, ThrOriginal.thrAt,
        ThrOriginal.posVal, gdesc, kindOf, bitsOf]
    · simp [SymSwitch.descAt, gdesc, kindOf, show ¬ n < 4 by omega, show ¬ n < 14 by omega,
        show n ≠ 15 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
        show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
        show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega]
  · rfl

/-! ## The docked writer, per mode -/

theorem tape_length (q : Nat) : (UnaryTemplate.tape q).length = q + 2 := by
  simp [UnaryTemplate.tape]

/-! ## The loop-region entry from its ports (generic in the producer) -/

/-- **The factor-loop entry, assembled from its ports.** If the header port holds `pad R (frame hdr)`, every
descriptor port `cslot P i (P.descSlots k)` holds `pad R (Dd i k)`, and every other region tape is blank, the
region IS `FactorLoop.entry P hdr Dd R` (FactorSelection's region conjunct). -/
theorem entry_of_ports {mode : Bool} {a : DecompositionAlgorithm} (P : FactorLoop.FactorProducer mode a pcpp)
    {U : Nat} (reg : Fin (19 + 4 * P.t) → Fin U) (hdr : List Bool) (Dd : Fin 4 → Fin P.d → List Bool)
    (R : Nat) (A' : Fin U → List Bool)
    (h0 : A' (reg ⟨0, by omega⟩) = ZeroPadding.pad R (RepairOrdinary.frame hdr))
    (hd : ∀ i k, A' (reg (FactorLoop.cslot P i (P.descSlots k))) = ZeroPadding.pad R (Dd i k))
    (hb : ∀ x : Fin (19 + 4 * P.t), x.val ≠ 0 → (∀ i k, FactorLoop.cslot P i (P.descSlots k) ≠ x) →
      A' (reg x) = List.replicate R false) :
    ∀ x, A' (reg x) = FactorLoop.entry P hdr Dd R x := by
  intro x
  by_cases hx0 : x.val = 0
  · have e : x = ⟨0, by omega⟩ := Fin.ext hx0
    rw [e, FactorLoop.entry_zero]
    exact h0
  by_cases h19 : 19 ≤ x.val
  · have hxl := x.isLt
    have ht : 0 < P.t := by omega
    have hi : (x.val - 19) / P.t < 4 := (Nat.div_lt_iff_lt_mul ht).mpr (by omega)
    have hj : (x.val - 19) % P.t < P.t := Nat.mod_lt _ ht
    have e : x = FactorLoop.cslot P ⟨(x.val - 19) / P.t, hi⟩ ⟨(x.val - 19) % P.t, hj⟩ := by
      apply Fin.ext
      simp only [FactorLoop.cslot]
      have := Nat.div_add_mod (x.val - 19) P.t
      rw [Nat.mul_comm] at this
      omega
    rw [e, FactorLoop.entry_cslot]
    by_cases hk : ∃ k, P.descSlots k = ⟨(x.val - 19) % P.t, hj⟩
    · obtain ⟨k, hk⟩ := hk
      rw [← hk, install_slot _ P.descInjective]
      exact hd _ k
    · rw [install_other _ _ _ _ (fun k e' => hk ⟨k, e'⟩), ← e]
      apply hb x hx0
      intro i k e'
      rw [e] at e'
      obtain ⟨_, e2⟩ := FactorLoop.cslot_inj P e'
      exact hk ⟨k, e2⟩
  · rw [FactorLoop.entry_small P hdr Dd R x hx0 (by omega)]
    apply hb x hx0
    intro i k e'
    have := FactorLoop.cslot_ge P i (P.descSlots k)
    rw [e'] at this
    omega

end


end
end NearCubicWires.SourceFactorSel.Modes
