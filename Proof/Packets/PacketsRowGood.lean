import Proof.Packets.PacketsLevelBound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.RowGood
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
open NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer.LiteralAlphabet (Good good_add good_zero)
noncomputable section

variable {S : Finset ℕ}

theorem good_parity : ∀ {n : ℕ} (ps : Fin n → StructuralGF2Polynomial), (∀ i, Good S (ps i)) →
    Good S (Normalized.structuralGF2FinParity ps)
  | 0, _, _ => good_zero S
  | _ + 1, ps, h => by
    rw [Normalized.structuralGF2FinParity]
    exact good_add (h 0) (good_parity _ (fun i => h i.succ))

theorem good_not {P : StructuralGF2Polynomial} (h : Good S P) : Good S (Normalized.structuralGF2Not P) :=
  good_add (good_one S) h

theorem good_ofFn {n : ℕ} (ps : Fin n → StructuralGF2Polynomial) (h : ∀ i, Good S (ps i)) :
    ∀ P ∈ List.ofFn ps, Good S P := by
  intro P hP
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
  exact h i

theorem good_selector {n : ℕ} (bits : Fin n → StructuralGF2Polynomial) (h : ∀ i, Good S (bits i))
    (target : BitInput n) : Good S (Normalized.structuralGF2BooleanSelector bits target) := by
  unfold Normalized.structuralGF2BooleanSelector
  apply good_product
  apply good_ofFn
  intro i
  split
  · exact h i
  · exact good_not (h i)

theorem good_truth {n : ℕ} (bits : Fin n → StructuralGF2Polynomial) (h : ∀ i, Good S (bits i))
    (f : BitInput n → Bool) : Good S (Normalized.structuralGF2TruthTable bits f) := by
  unfold Normalized.structuralGF2TruthTable
  apply good_parity
  intro code
  split
  · exact good_selector bits h _
  · exact good_zero S

theorem good_majority {n : ℕ} (bits : Fin n → StructuralGF2Polynomial) (h : ∀ i, Good S (bits i)) :
    Good S (Normalized.structuralGF2BitMajority bits) :=
  good_truth bits h _

theorem good_lookup {pb : ℕ} (lookup : Fin (pb + 1) → Bool) (oneHot : Fin (pb + 1) → StructuralGF2Polynomial)
    (h : ∀ c, Good S (oneHot c)) : Good S (Normalized.structuralGF2OneHotLookup lookup oneHot) := by
  unfold Normalized.structuralGF2OneHotLookup
  apply good_parity
  intro c
  split
  · exact h c
  · exact good_zero S

theorem good_conjunction {n : ℕ} (values : Fin n → StructuralGF2Polynomial) (h : ∀ i, Good S (values i)) :
    Good S (Normalized.structuralGF2FiniteConjunction values) :=
  good_product _ (good_ofFn values h)

theorem good_radix {digits pb : ℕ} (modulus offset base : ℕ)
    (oneHot : Fin digits → Fin (pb + 1) → StructuralGF2Polynomial) (h : ∀ d c, Good S (oneHot d c)) :
    Good S (Normalized.structuralGF2ModularRadixRow modulus offset base oneHot) := by
  unfold Normalized.structuralGF2ModularRadixRow
  apply good_parity
  intro code
  dsimp only
  split
  · exact good_conjunction _ (fun d => h _ _)
  · exact good_zero S

theorem coord_good {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)
    (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den) (cand : Fin (occ.length + 1)) :
    Good (Finset.range occ.length) (LiveRows.coordinatePoly true occ I den M sample cand) := by
  rw [coordinate_eq]
  exact good_majority _ (fun time => literalVec_good occ I den M sample time cand)

/-- **Every closeout row polynomial is normal and supported in the occurrence codes.** -/
theorem row_good (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) :
    Good (Finset.range (r.family a).occurrences.length) (rcDecode a r k).polynomial := by
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target =>
    show Good _ (LiveRows.symPolynomial true r0 _ _ k.seed k.offset)
    unfold LiveRows.symPolynomial
    exact good_conjunction _ (fun i => good_lookup _ _ (fun c => coord_good _ _ _ _ _ c))
  | thr r0 four L target =>
    show Good _ (LiveRows.thrPolynomial true a r0 _ _ k.selection k.prime.val k.residue.val k.seed)
    unfold LiveRows.thrPolynomial
    exact good_radix _ _ _ _ (fun d c => coord_good _ _ _ _ _ c)

/-- The row polynomial has the row's declared degree (accepted `PCJc06b3608d6d34481_Rows`). -/
theorem row_degree (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) :
    Ring.Degree (rcDecode a r k).degree (rcDecode a r k).polynomial := by
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target => exact PCJc06b3608d6d34481_Rows.sym_degree r0 _ _ k.seed k.offset
  | thr r0 four L target =>
    exact PCJc06b3608d6d34481_Rows.thr_degree a r0 _ _ k.selection k.prime.val k.residue.val k.seed

end
end NearCubicWires.PacketsConstruction.RowGood
