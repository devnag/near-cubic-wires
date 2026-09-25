import Proof.SourceAssembly.SourceSkelSeam3

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
namespace NearCubicWires.SourceSkeleton
noncomputable section

section bridge
variable (sources : EightSources) (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)
  {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
    ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat)

/-- The admission's layout family, in the seam's request form. -/
def layoutAtOf : (mode : Bool) → SourceConstruction.TraceData.LayoutFamily coordinate ph ci sources L target mode selector →
    ∀ m : Nat, Packets.Layout (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
  | true, lay => lay
  | false, lay => lay

include compiler in
/-- The compiler's facts, in the seam's request form. -/
theorem factsAtOf : ∀ (mode : Bool) (m : Nat), ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
    Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)) row
  | true, m, row, hrow => compiler sources L target true (SourceRequest.FactorLoop.factorsAt coordinate ph ci m) _ row hrow
  | false, m, row, hrow => compiler sources L target false (SourceRequest.FactorLoop.factorsAt coordinate ph ci m) _ row hrow

/-- **The data list of call `m`**: S's `TraceData.dsOf` IS the seam's `dataList … (requestAt … m) …`. -/
theorem ds_bridge (mode : Bool) (lay : SourceConstruction.TraceData.LayoutFamily coordinate ph ci sources L target mode selector)
    (m : Nat) :
    SourceConstruction.TraceData.dsOf coordinate ph ci sources L target mode selector compiler lay m =
      dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
        (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
        (layoutAtOf sources selector coordinate ph ci L target mode lay m)
        (factsAtOf sources selector compiler coordinate ph ci L target mode m) := by
  revert lay
  cases mode <;> intro lay <;> rfl

/-- **The child-list length of call `m`**: S's `TraceData.lenOf` IS the seam's `(exactListWord (cacheArgs …).gs).length`. -/
theorem len_bridge (mode : Bool) (m : Nat) :
    SourceConstruction.TraceData.lenOf coordinate ph ci sources L target mode m =
      (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
        ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))).gs).length := by
  cases mode <;> rfl

/-- **The row width of call `m`** in the seam's form, from the slope identity (S) and the `U0` identity. -/
theorem rw_bridge (mode : Bool) (deg : Nat → Nat) (Mb Ms U0 : Nat)
    (hslope : ∀ m, SourceConstruction.Native.M2Of (deg m) (normalizedLiveCount q L) =
      if 3 < SourceConstruction.TraceData.lenOf coordinate ph ci sources L target mode m then Mb else Ms)
    (hU0 : SourceConstruction.Native.U0Of q (normalizedLiveCount q L) = U0) (m : Nat) :
    SourceConstruction.TraceData.rowWidthOf coordinate ph ci sources L target mode deg m =
      RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))).gs).length := by
  unfold SourceConstruction.TraceData.rowWidthOf
  rw [hslope m, hU0, len_bridge sources coordinate ph ci L target mode m]

end bridge

/-- **The slope identity from the effective degree** (arithmetic): with `Ms = 2(K+1)` and `Mb = d0·Ms`, a degree `1` or `d0` chosen by the
child-list length gives the seam's slope. -/
theorem slope_of_deg (K Mb Ms d0 dg len : Nat) (hMs : Ms = 2 * (K + 1)) (hMb : Mb = d0 * Ms)
    (hdg : dg = if 3 < len then d0 else 1) :
    SourceConstruction.Native.M2Of dg K = if 3 < len then Mb else Ms := by
  unfold SourceConstruction.Native.M2Of
  subst hMs hMb hdg
  split_ifs <;> ring

/-- **`U0`**: S's `U0Of q K` is SI's master value `3(K+3) + 2⌈(q-K)/2⌉` (`InitRun.U0 L q` at `K = normalizedLiveCount q L`). -/
theorem U0Of_eq (q K : Nat) :
    SourceConstruction.Native.U0Of q K = 3*(K+2+1) + ((q - K+1)/2 + (q - K+1)/2) := by
  unfold SourceConstruction.Native.U0Of; omega

end
end NearCubicWires.SourceSkeleton
end
