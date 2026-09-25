import Proof.SourceAssembly.SourceRequestSymOriginal

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics ExecutableInterfaces
noncomputable section
namespace NearCubicWires.SourceRequest.SelOrigCost
open PCJd4d1d9d7d1fa4313_Production

/-! ## Powers of `S + 1` -/

theorem up (S c e E x : Nat) (he : e ≤ E) (h : x ≤ c * (S + 1) ^ e) : x ≤ c * (S + 1) ^ E :=
  h.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega) he))

theorem lin_le (S E : Nat) (hE : 1 ≤ E) : S + 1 ≤ (S + 1) ^ E := by
  have h := Nat.pow_le_pow_right (show 0 < S + 1 by omega) hE
  rw [pow_one] at h
  exact h

/-- The writer's fuel is quadratic in `S`. -/
theorem wFuel_le (P q N S : Nat) (hP : P ≤ S) (hq : q ≤ S) (hN : N ≤ S) :
    1 + 1 + CloseoutRowsSupportStream.circuitBudget P q N ≤ 6002 * (S + 1) ^ 2 := by
  unfold CloseoutRowsSupportStream.circuitBudget
  have h1 : (N + 2) * (P + q + 1) ≤ (S + 2) * (2 * S + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : (S + 2) * (2 * S + 1) + (S * S + S + 1) = 3 * (S + 1) ^ 2 := by ring
  have e2 : 2000 * (N + 2) * (P + q + 1) = 2000 * ((N + 2) * (P + q + 1)) := by ring
  have h2 : 1 ≤ (S + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-! ## The THR original factor -/

/-- The THR original factor's coefficient. -/
def thrOC (a : DecompositionAlgorithm) : Nat := 3000 * (a.coefficient + 2) ^ 2 + 30000

/-- The THR original factor's exponent. -/
def thrOE (a : DecompositionAlgorithm) : Nat := 2 * a.degree + 2

/-- The decomposition entry's budget at the retained top gate. -/
theorem entry_le (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) (S : Nat)
    (hr : r.arity + r.gate.encodingBits + 1 ≤ S + 1) :
    DecompositionSource.Entry.budget a r ≤ 1024 * ((a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a) := by
  have h := DecompositionSource.entry_budget_coarse a r
  have hsb : DecompositionSource.sourceBudget a r ≤ a.coefficient * (S + 1) ^ (a.degree + 1) := by
    unfold DecompositionSource.sourceBudget
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hr _).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hpar : DecompositionSource.parameter r + 1 ≤ 2 * (S + 1) ^ (a.degree + 1) := by
    unfold DecompositionSource.parameter
    have := lin_le S (a.degree + 1) (by omega)
    omega
  have hB : DecompositionSource.sourceBudget a r + DecompositionSource.parameter r + 1 ≤
      (a.coefficient + 2) * (S + 1) ^ (a.degree + 1) := by
    rw [Nat.add_mul]; omega
  have hsq := Nat.pow_le_pow_left hB 2
  have e : ((a.coefficient + 2) * (S + 1) ^ (a.degree + 1)) ^ 2 = (a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a := by
    unfold thrOE; rw [mul_pow, ← pow_mul]; ring_nf
  rw [e] at hsq
  omega

/-- The decomposition entry's output word. -/
theorem output_le (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) (S : Nat)
    (hr : r.arity + r.gate.encodingBits + 1 ≤ S + 1) (hn : 2 * natBitLength r.arity + 1 ≤ S + 1) :
    (DecompositionSource.Entry.output a r).length ≤ (a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a := by
  unfold DecompositionSource.Entry.output
  rw [List.length_append, DecompositionSource.natWord_length]
  have ho := DecompositionSource.output_length a r
  have hsb : DecompositionSource.sourceBudget a r ≤ a.coefficient * (S + 1) ^ thrOE a := by
    unfold DecompositionSource.sourceBudget thrOE
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hr _).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hl := lin_le S (thrOE a) (by unfold thrOE; omega)
  have hc : a.coefficient + 1 ≤ (a.coefficient + 2) ^ 2 := by nlinarith
  have hm : (a.coefficient + 1) * (S + 1) ^ thrOE a ≤ (a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a := Nat.mul_le_mul_right _ hc
  rw [Nat.add_mul, one_mul] at hm
  omega

/-- **The THR original factor's cost** is `≤ thrOC a · (S+1)^(2·a.degree+2)` once `S` dominates `q`, `P`, the code width and the factor's
native word, support stream and TOP content. -/
theorem thrOrig_le (a : DecompositionAlgorithm) {q : Nat} (c : NormalizedThresholdThresholdCircuit q) (P L S : Nat)
    (hq : q ≤ S) (hP : P ≤ S) (hcw : ThrSwitch.codeWidth L ≤ S)
    (hN : (thrWord c).length ≤ S) (hS : (ThrOriginal.stream c).length ≤ S)
    (hT : (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c)).length ≤ S) :
    ThrOriginal.cost a c P (ThrSwitch.codeBits L c) ≤ thrOC a * (S + 1) ^ thrOE a := by
  have hE : 2 ≤ thrOE a := by unfold thrOE; omega
  have hw := wFuel_le P q (ThrSwitch.codeBits L c).length S hP hq (by rw [ThrSwitch.codeBits_length]; exact hcw)
  have hwE := up S 6002 2 (thrOE a) _ hE hw
  -- the pieces of `thrWord c`
  have hN' := hN
  unfold thrWord at hN'
  simp only [List.length_append, frame_length, DecompositionSource.natWord_length] at hN'
  have htw := DecompositionSource.thresholdWord_length (nonStrictAsStrict (retainedTopGate c))
  have hl := lin_le S (thrOE a) (by omega)
  have hen := entry_le a ⟨c.top.support.card, nonStrictAsStrict (retainedTopGate c)⟩ S (by
    show c.top.support.card + (nonStrictAsStrict (retainedTopGate c)).encodingBits + 1 ≤ S + 1
    omega)
  have hou := output_le a ⟨c.top.support.card, nonStrictAsStrict (retainedTopGate c)⟩ S (by
    show c.top.support.card + (nonStrictAsStrict (retainedTopGate c)).encodingBits + 1 ≤ S + 1
    omega) (by
    show 2 * natBitLength c.top.support.card + 1 ≤ S + 1
    omega)
  unfold ThrOriginal.cost PCJ6e421fabe2aa4155_SourceTopNative.budget PCJ6e421fabe2aa4155_SourceTopExtract.budget
    PCJ6e421fabe2aa4155_SourceTopExtract.rawBudget PCJ6e421fabe2aa4155_SourceTopEntry.budget
  simp only [ThrOriginal.wFuel] at hwE ⊢
  have e : thrOC a * (S + 1) ^ thrOE a =
      3000 * ((a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a) + 30000 * (S + 1) ^ thrOE a := by
    unfold thrOC; ring
  rw [e]
  have hcq : (S + 1) ^ thrOE a ≤ (a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a :=
    Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by omega))
  show _ ≤ _
  omega

/-! ## The SYM original factor -/

/-- **The SYM original factor's cost** is `≤ 30000 · (S+1)^2`. -/
theorem symOrig_le {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) (P L S : Nat)
    (hq : q ≤ S) (hP : P ≤ S) (hcw : SymOriginal.symCodeWidth L ≤ S)
    (hN : (symWord c).length ≤ S) (hS : (SymOriginal.stream c).length ≤ S) :
    SymOriginal.cost c P (SymOriginal.symCodeBits L c) ≤ 30000 * (S + 1) ^ 2 := by
  have hw := wFuel_le P q (SymOriginal.symCodeBits L c).length S hP hq
    (by rw [SymOriginal.symCodeBits_length]; exact hcw)
  have hl := lin_le S 2 (by omega)
  unfold SymOriginal.cost
  simp only [ThrOriginal.wFuel] at hw ⊢
  omega

end NearCubicWires.SourceRequest.SelOrigCost
end

