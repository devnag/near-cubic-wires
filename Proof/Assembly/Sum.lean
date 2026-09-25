import Proof.Assembly.Plan
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJ843c22a3684945e9_Plan
open scoped BigOperators
namespace PCJ843c22a3684945e9_Sum
noncomputable section

def splitProduct {n : Nat} (bounds : Fin (n+1) → Nat) :
    ((i : Fin (n+1)) → Fin (bounds i)) ≃
      Fin (bounds 0) × ((i : Fin n) → Fin (bounds i.succ)) where
  toFun f := (f 0,fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by cases p; rfl

theorem finiteProduct_sum (n : Nat) (bounds : Fin n → Nat)
    (f : ((i : Fin n) → Fin (bounds i)) → Nat) :
    ((Packets.finiteProduct n bounds).map f).sum = ∑ x, f x := by
  induction n with
  | zero =>
    simp only [Packets.finiteProduct,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Fintype.sum_unique]
    congr 1
  | succ n ih =>
    rw [Packets.finiteProduct,C10ExternalRowLoop.sum_map_flatMap]
    simp only [List.map_map,Function.comp_def]
    simp_rw [ih]
    simp only [List.finRange,List.map_ofFn,List.sum_ofFn]
    have h := Equiv.sum_comp (splitProduct bounds).symm f
    rw [Fintype.sum_prod_type] at h
    exact h

theorem seed_sum {q : Nat} (occ : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (den : Nat) (f : LiveRows.Seed occ I den → Nat) :
    ((Packets.seedList occ I den).map f).sum = ∑ e, f e := by
  simp only [Packets.seedList,List.map_ofFn,List.sum_ofFn]
  exact Equiv.sum_comp _ f

theorem prime_sum (cutoff : Nat) (f : PrimeIndex cutoff → Nat) :
    ((List.ofFn (primeIndexFinEquiv cutoff).symm).map f).sum = ∑ p, f p := by
  simp only [List.map_ofFn,List.sum_ofFn]
  exact Equiv.sum_comp _ f

theorem join_off {q : Nat} (I : Finset (Fin q))
    (y y' : BitInput I.card) (z : BitInput Iᶜ.card)
    (i : Fin q) (hi : i ∉ I) :
    C10SupplierRowInput.joinInput I y z i = C10SupplierRowInput.joinInput I y' z i := by
  obtain ⟨j,rfl⟩ := (normalizedLiveExternalCoordinateEquiv I).surjective i
  rw [C10SupplierRowInput.joinInput_coord,C10SupplierRowInput.joinInput_coord]
  cases j with
  | inl j =>
    exfalso
    apply hi
    unfold normalizedLiveExternalCoordinateEquiv
    rw [finSumEquivOfFinset_inl]
    exact Finset.orderEmbOfFin_mem _ rfl j
  | inr j => rfl

theorem constant_join {q : Nat} (occ : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (y y' : BitInput I.card) (z : BitInput Iᶜ.card)
    (i : Fin occ.length) :
    occurrenceResidualConstant occ I (C10SupplierRowInput.joinInput I y z) i =
      occurrenceResidualConstant occ I (C10SupplierRowInput.joinInput I y' z) i :=
  C10PrinterBridge.residualConstant_congr _ I _ _ (join_off I y y' z)

theorem symOffsets_join (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (y y' : BitInput I.card) (z : BitInput Iᶜ.card) :
    LiveRows.symOffsets r I (C10SupplierRowInput.joinInput I y z) =
      LiveRows.symOffsets r I (C10SupplierRowInput.joinInput I y' z) := by
  funext i
  unfold LiveRows.symOffsets LiveRows.constantCount
  simp_rw [constant_join _ I y y' z]

theorem modularOffset_join {q : Nat} (occ : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (y y' : BitInput I.card) (z : BitInput Iᶜ.card)
    (e : LabelledEquation (Fin occ.length)) (p : Nat) :
    LiveRows.modularOffset occ I (C10SupplierRowInput.joinInput I y z) e p =
      LiveRows.modularOffset occ I (C10SupplierRowInput.joinInput I y' z) e p := by
  unfold LiveRows.modularOffset
  simp_rw [constant_join _ I y y' z]

theorem sum_join {q : Nat} (I : Finset (Fin q)) (f : BitInput q → Nat) :
    (∑ z : BitInput Iᶜ.card, ∑ y : BitInput I.card,
      f (C10SupplierRowInput.joinInput I y z)) = ∑ x, f x := by
  rw [Finset.sum_comm]
  have h := Equiv.sum_comp (normalizedLiveExternalInputEquiv I).symm f
  rw [Fintype.sum_prod_type] at h
  exact h

theorem sym_bound (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (x : BitInput r.q) (i : Fin r.circuits.length) :
    LiveRows.symOffsets r I x i < (r.circuits.get i).bottomCount+1 := by
  have h : LiveRows.symOffsets r I x i ≤ (symmetricCircuitMask r i).card := by
    unfold LiveRows.symOffsets LiveRows.constantCount
    calc
      _ ≤ ∑ _j ∈ symmetricCircuitMask r i, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        cases occurrenceResidualConstant (symmetricFourfoldOccurrences r) I x j <;> decide
      _ = _ := by simp
  rw [symmetricCircuitMask_card] at h
  omega

def symBounded (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (x : BitInput r.q) (i : Fin r.circuits.length) :
    Fin ((r.circuits.get i).bottomCount+1) :=
  ⟨LiveRows.symOffsets r I x i,sym_bound r I x i⟩

theorem sym_eq (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (x : BitInput r.q)
    (v : (i : Fin r.circuits.length) → Fin ((r.circuits.get i).bottomCount+1)) :
    (LiveRows.symOffsets r I x = fun i => (v i).val) ↔ symBounded r I x = v := by
  constructor
  · intro h; funext i; exact Fin.ext (congrFun h i)
  · intro h; exact congrArg (fun f i => (f i).val) h

theorem modular_bound {q cutoff : Nat} (occ : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (x : BitInput q) (e : LabelledEquation (Fin occ.length))
    (p : PrimeIndex cutoff) : LiveRows.modularOffset occ I x e p.val < p.val := by
  have hp : (0 : Int) < p.val := by exact_mod_cast (mem_primesUpTo.mp p.property).1.pos
  unfold LiveRows.modularOffset
  have hn := Int.emod_nonneg
    ((∑ i, e.weights i * ((occurrenceResidualConstant occ I x i).toNat : Int)) - e.target)
    (ne_of_gt hp)
  have hl := Int.emod_lt_of_pos
    ((∑ i, e.weights i * ((occurrenceResidualConstant occ I x i).toNat : Int)) - e.target) hp
  omega

/- Collapse selectors before inserting any large polynomial expression. -/
theorem sym_selected_sum (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (V : (Fin r.circuits.length → Nat) → BitInput r.q → Nat) :
    (∑ offset : (i : Fin r.circuits.length) → Fin ((r.circuits.get i).bottomCount+1),
      ∑ z : BitInput Iᶜ.card,
        if decide (LiveRows.symOffsets r I (C10SupplierRowInput.joinInput I (fun _ => false) z) =
            fun i => (offset i).val)
        then ∑ y : BitInput I.card, V (fun i => (offset i).val) (C10SupplierRowInput.joinInput I y z)
        else 0) = ∑ x : BitInput r.q, V (LiveRows.symOffsets r I x) x := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ z : BitInput Iᶜ.card, ∑ y : BitInput I.card,
        V (LiveRows.symOffsets r I (C10SupplierRowInput.joinInput I y z))
          (C10SupplierRowInput.joinInput I y z) := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [decide_eq_true_eq,sym_eq]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      apply Finset.sum_congr rfl
      intro y hy
      dsimp only [symBounded]
      rw [symOffsets_join r I (fun _ => false) y z]
    _ = _ := sum_join I (fun x => V (LiveRows.symOffsets r I x) x)

theorem modular_selected_sum {q cutoff : Nat} (occ : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (equation : LabelledEquation (Fin occ.length)) (p : PrimeIndex cutoff)
    (V : Nat → BitInput q → Nat) :
    (∑ offset : Fin p.val, ∑ z : BitInput Iᶜ.card,
      if decide (LiveRows.modularOffset occ I (C10SupplierRowInput.joinInput I (fun _ => false) z)
          equation p.val = offset.val)
      then ∑ y : BitInput I.card, V offset.val (C10SupplierRowInput.joinInput I y z)
      else 0) = ∑ x : BitInput q, V (LiveRows.modularOffset occ I x equation p.val) x := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ z : BitInput Iᶜ.card, ∑ y : BitInput I.card,
        V (LiveRows.modularOffset occ I (C10SupplierRowInput.joinInput I y z) equation p.val)
          (C10SupplierRowInput.joinInput I y z) := by
      apply Finset.sum_congr rfl
      intro z hz
      let wanted : Fin p.val := ⟨LiveRows.modularOffset occ I
        (C10SupplierRowInput.joinInput I (fun _ => false) z) equation p.val,
        modular_bound occ I _ _ p⟩
      have hh : ∀ offset : Fin p.val,
          (LiveRows.modularOffset occ I (C10SupplierRowInput.joinInput I (fun _ => false) z)
            equation p.val = offset.val) ↔ wanted = offset := by
        intro offset
        constructor
        · intro h; exact Fin.ext h
        · intro h; exact congrArg Fin.val h
      simp only [decide_eq_true_eq,hh,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      apply Finset.sum_congr rfl
      intro y hy
      dsimp only [wanted]
      rw [modularOffset_join occ I (fun _ => false) y z]
    _ = _ := sum_join I (fun x => V (LiveRows.modularOffset occ I x equation p.val) x)

theorem sym_sum (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat) :
    familySum (Packets.symFamily r L target) = LiveRows.symNumerator r L target := by
  let I := CyclicChoice.live (symmetricFourfoldOccurrences r) L
  let den := symmetricListDenominator r target
  unfold familySum Packets.symFamily
  dsimp only
  rw [C10ExternalRowLoop.sum_map_flatMap,seed_sum]
  simp only [List.map_map,Function.comp_def]
  change (∑ e : LiveRows.Seed (symmetricFourfoldOccurrences r) I den,
    ((Packets.symOffsetList r).map (fun offset =>
      ∑ z : BitInput Iᶜ.card,
        if decide (LiveRows.symOffsets r I (C10SupplierRowInput.joinInput I (fun _ => false) z) = offset)
        then ∑ y : BitInput I.card,
          (evaluateStructuralGF2 (LiveRows.residualAssignment (symmetricFourfoldOccurrences r) I
            (C10SupplierRowInput.joinInput I y z)) (LiveRows.symPolynomial false r I den e offset)).toNat
        else 0)).sum) = _
  unfold Packets.symOffsetList
  simp only [List.map_map,Function.comp_def]
  simp_rw [finiteProduct_sum]
  change _ = ∑ e : LiveRows.Seed (symmetricFourfoldOccurrences r) I den,
    ∑ x : BitInput r.q, (LiveRows.symRow r I den x e).toNat
  apply Finset.sum_congr rfl
  intro e he
  exact sym_selected_sum r I (fun offset x =>
    (evaluateStructuralGF2 (LiveRows.residualAssignment (symmetricFourfoldOccurrences r) I x)
      (LiveRows.symPolynomial false r I den e offset)).toNat)

theorem thr_sum (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat) :
    familySum (Packets.thrFamily a r L target) = LiveRows.thrNumerator a r L target := by
  let occ := thresholdFourfoldOccurrences r
  let I := CyclicChoice.live occ L
  let den := CloseoutFinalC10ThresholdRows.listDenominator a r target
  let cutoff := CloseoutFinalC10ThresholdRows.primeCutoff a r target
  unfold familySum Packets.thrFamily
  dsimp only
  rw [C10ExternalRowLoop.sum_map_flatMap]
  unfold Packets.thrSelectionList
  rw [finiteProduct_sum]
  change _ = ∑ sel : ThresholdRows.Selection a r, ∑ p : PrimeIndex cutoff,
    ∑ e : LiveRows.Seed occ I den, ∑ x : BitInput r.q,
      (LiveRows.thrSelectionRow a r I den x sel p e).toNat
  apply Finset.sum_congr rfl
  intro sel hsel
  rw [C10ExternalRowLoop.sum_map_flatMap,prime_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [C10ExternalRowLoop.sum_map_flatMap,seed_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [List.finRange,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  change (∑ offset : Fin p.val, ∑ z : BitInput Iᶜ.card,
    if decide (LiveRows.modularOffset occ I (C10SupplierRowInput.joinInput I (fun _ => false) z)
      (ThresholdRows.equation a r sel) p.val = offset.val)
    then ∑ y : BitInput I.card,
      (evaluateStructuralGF2 (LiveRows.residualAssignment occ I (C10SupplierRowInput.joinInput I y z))
        (LiveRows.thrPolynomial false a r I den sel p.val offset.val e)).toNat
    else 0) = _
  exact modular_selected_sum occ I (ThresholdRows.equation a r sel) p (fun offset x =>
    (evaluateStructuralGF2 (LiveRows.residualAssignment occ I x)
      (LiveRows.thrPolynomial false a r I den sel p.val offset e)).toNat)

theorem certificate : RequestSum := by
  intro sources L target mode q circuit pcpp atoms
  cases mode with
  | false => exact thr_sum (decompositionOf sources) _ L target
  | true => exact sym_sum _ L target
end
end PCJ843c22a3684945e9_Sum
