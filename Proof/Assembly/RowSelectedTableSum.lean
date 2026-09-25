import Proof.Assembly.Plan
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.MatrixScoreBatch NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJ843c22a3684945e9_Plan
open scoped BigOperators
namespace PCJ843c22a3684945e9_Row
noncomputable section
variable {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)
  (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows)
  (facts : Packets.PacketFacts a F g r)

include facts in
theorem one_value (yi : Fin (C10SupplierRowInput.liveList (Packets.live F)).length)
    (rowN colN : Nat) :
    CompetitorRowCountMeaning.occurrence
      (CloseoutRowsCacheInput.polynomial (Packets.pool a F g)
        (ExtIncidence.rawRows (Packets.one a F g r yi))) rowN colN % 2 =
      (evaluateStructuralGF2
        (LiveRows.residualAssignment F.occurrences (Packets.live F)
          (C10SupplierRowInput.joinInput (Packets.live F)
            (BinaryPool.assignmentAt (Packets.live F) yi.val)
            (C10ExternalRowLoop.printerPoint (Packets.live F) (Packets.residual F) g.arity rowN colN)))
        r.reference).toNat := by
  have hstep := (exactPolynomialValue_toNat
    (fun (e : RowBinLift.Equation ((Packets.residual F+1)/2) (Packets.residual F/2))
      (_ : Unit) (_ : Unit) => decide (e.Holds (RowBinLift.assignment rowN colN)))
    (CloseoutRowsCacheInput.polynomial (Packets.pool a F g)
      (ExtIncidence.rawRows (Packets.one a F g r yi))) () ()).symm
  change CompetitorRowCountMeaning.occurrence _ _ _ % 2 = _ at hstep
  rw [hstep,ExtIncidence.raw_polynomial_value]
  simp_rw [C10SupplierRowInput.coordinates_holds]
  exact congrArg Bool.toNat (facts.2 yi
    (C10SupplierRowInput.halfPoint ((Packets.residual F+1)/2) (Packets.residual F/2) rowN colN))

def column (z : BitInput (Packets.live F)ᶜ.card) : Nat :=
  ∑ y : BitInput (Packets.live F).card,
    (evaluateStructuralGF2
      (LiveRows.residualAssignment F.occurrences (Packets.live F)
        (C10SupplierRowInput.joinInput (Packets.live F) y z)) r.reference).toNat

include facts in
theorem count_value (rowN colN : Nat) :
    CompetitorRowCountMeaning.count
      (CloseoutRowsCacheInput.family (Packets.pool a F g)
        (ExtIncidence.NativeRowInput.bank (Packets.packets a F g r))) rowN colN =
      column F r (C10ExternalRowLoop.printerPoint (Packets.live F) (Packets.residual F) g.arity rowN colN) := by
  simp only [CompetitorRowCountMeaning.count,CloseoutRowsCacheInput.family,
    ExtIncidence.NativeRowInput.bank,Packets.packets,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  simp_rw [one_value a F g r facts]
  exact BinaryPool.sum_assignmentAt (Packets.live F) (M:=Nat) (fun y =>
    (evaluateStructuralGF2
      (LiveRows.residualAssignment F.occurrences (Packets.live F)
        (C10SupplierRowInput.joinInput (Packets.live F) y
          (C10ExternalRowLoop.printerPoint (Packets.live F) (Packets.residual F) g.arity rowN colN)))
      r.reference).toNat)

theorem certificate : RowCertificate := by
  intro q L a F g layout r hr facts
  letI := Packets.radix a F g layout
  letI := Packets.bankDegree a F g layout r hr facts
  constructor
  · intro i j
    change CompetitorRowCountMeaning.count _ i.val j.val < 2^((Packets.live F).card+1)
    apply (CompetitorRowCountMeaning.count_le_length _ i.val j.val).trans_lt
    rw [CompactNativeRequest.family_eq,CloseoutRowsCacheInput.family_length]
    simp only [ExtIncidence.NativeRowInput.bank,Packets.packets,List.length_map,List.length_ofFn,
      C10SupplierRowInput.liveList_length]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  constructor
  · intro i j
    exact P1CompactInput.count_modEq (Packets.residual F) ((Packets.live F).card+1)
      layout.w (Packets.pool a F g) (ExtIncidence.NativeRowInput.bank (Packets.packets a F g r))
      layout.residualLarge (Packets.gate a F g layout r hr facts)
      (ExtIncidence.NativeRowInput.bank_width (Packets.packets a F g r) layout.w
        (Packets.width a F g layout r hr facts)) i j
  · rw [PCJ9eff70d512234a4c_Fixed.datumValue,RowExternalSelection.cells_selected_sum]
    have htable : ∀ i j,
        (Packets.datum a F g layout r hr facts).f i j =
          column F r (C10ExternalRowLoop.printerPoint (Packets.live F) (Packets.residual F)
            g.arity i.val j.val) := by
      intro i j
      change CompetitorRowCountMeaning.count _ i.val j.val = _
      rw [CompactNativeRequest.family_eq]
      exact count_value a F g r facts i.val j.val
    simp_rw [htable]
    let G : BitInput (Packets.live F)ᶜ.card → Nat := fun z => if r.select z then column F r z else 0
    change RowExternalSelection.total (Packets.rowInput a F g layout r hr facts).odd
      (fun i j => G (C10ExternalRowLoop.printerPoint (Packets.live F) (Packets.residual F)
        g.arity i.val j.val)) = _
    have half := C10SupplierSelect.total_eq_sum_half (Packets.live F)
      (fun i j => G (C10ExternalRowLoop.printerPoint (Packets.live F) (Packets.residual F) g.arity i j))
      (EquationRow.request (Packets.rowInput a F g layout r hr facts)).U
      (Packets.rowInput a F g layout r hr facts).odd
      (by change 2^((Packets.residual F+1)/2) = _
          rw [C10ExternalRowLoop.harity_right (Packets.live F) (Packets.residual F) g.arity])
      (by change decide (Packets.residual F % 2 = 1) = _
          rw [C10ExternalRowLoop.harity_card (Packets.live F) (Packets.residual F) g.arity])
    exact half.trans (C10ExternalRowLoop.sum_printerPoint (Packets.live F) (Packets.residual F) g.arity
      (normalizedExternalRightCount (Packets.live F)) (normalizedExternalLeftCount (Packets.live F))
      (C10ExternalRowLoop.harity_right (Packets.live F) (Packets.residual F) g.arity).symm
      (C10ExternalRowLoop.harity_left (Packets.live F) (Packets.residual F) g.arity).symm G)
end
end PCJ843c22a3684945e9_Row
