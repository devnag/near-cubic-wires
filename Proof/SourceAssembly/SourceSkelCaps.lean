import Proof.SourceAssembly.SourceSkelLayoutW

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
namespace NearCubicWires.SourceSkeleton
noncomputable section

/-- Four caps fixed once. -/
def capsU (hF cC dR rR : Nat) : PCJd4d1d9d7d1fa4313_Production.RowCaps :=
  { headerFuel := hF, copyCap := cC, descriptorReserve := dR, rawReserve := rR }


/-- **`RowCaps.Good` is monotone in every cap.** -/
theorem good_mono {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    {r : PCJd4d1d9d7d1fa4313_Production.Request} {layout : Packets.Layout a (r.family a) (geometryOf selector a r)}
    {facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row}
    {c c' : PCJd4d1d9d7d1fa4313_Production.RowCaps}
    (h : PCJd4d1d9d7d1fa4313_Production.RowCaps.Good selector a printer r layout facts c)
    (h1 : c.headerFuel ≤ c'.headerFuel) (h2 : c.copyCap ≤ c'.copyCap) (h3 : c.descriptorReserve ≤ c'.descriptorReserve)
    (h4 : c.rawReserve ≤ c'.rawReserve) :
    PCJd4d1d9d7d1fa4313_Production.RowCaps.Good selector a printer r layout facts c' :=
  ⟨fun row hr => (h.1 row hr).trans h1, fun row hr i => (h.2.1 row hr i).trans h2, h.2.2.1.trans h4, h.2.2.2.trans h3⟩

/-- **The uniform caps are good at every call below them** (from `chosen_good` at the call's layout, `streamCap ≤ C`). -/
theorem goodAt_uniform (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (r : PCJd4d1d9d7d1fa4313_Production.Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (hC : RCFive.NativeResources.streamCap a (r.family a) (geometryOf selector a r) layout ≤ layout.C)
    (hF cC dR rR : Nat)
    (h1 : (RCFive.RowCaps.chosen selector a printer r layout).headerFuel ≤ hF)
    (h2 : (RCFive.RowCaps.chosen selector a printer r layout).copyCap ≤ cC)
    (h3 : (RCFive.RowCaps.chosen selector a printer r layout).descriptorReserve ≤ dR)
    (h4 : (r.raw selector a).length ≤ rR) :
    PCJd4d1d9d7d1fa4313_Production.RowCaps.Good selector a printer r layout facts (capsU hF cC dR rR) :=
  good_mono (RCFive.RowCaps.chosen_good selector a printer r layout facts hC) h1 h2 h3 h4

end
end NearCubicWires.SourceSkeleton
end
