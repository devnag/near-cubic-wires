import Proof.SourceAssembly.SourceClauseChain

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
namespace NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- The family step's entry-emitter words at call `j` (`_hrefill`'s `outA`'s `enc` part). -/
abbrev encWOf {Atom : Type} {U : Nat} (b : Nat) (vd : RCFive.Source.CallValues Atom U) (j : Nat) :=
  e_bank b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j)
    (ZeroPadding.pad (vd.D j) (Stream.entryWord b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩))

/-- `install app (install enc X E) T` does not read `X` on the `enc`/`app` tapes. -/
theorem install_cov {t2 t3 u : Nat} (enc : Fin t2 → Fin u) (app : Fin t3 → Fin u) (henc : Function.Injective enc)
    (happ : Function.Injective app) (X Y : Fin u → List Bool) (E : Fin t2 → List Bool) (T : Fin t3 → List Bool) (x : Fin u)
    (hx : (∃ i, enc i = x) ∨ (∃ i, app i = x)) :
    install app (install enc X E) T x = install app (install enc Y E) T x := by
  by_cases ha : ∃ i, app i = x
  · obtain ⟨i, rfl⟩ := ha
    rw [install_slot _ happ, install_slot _ happ]
  · have ha' : ∀ i, app i ≠ x := fun i h => ha ⟨i, h⟩
    rw [install_other _ _ _ x ha', install_other _ _ _ x ha']
    rcases hx with ⟨i, rfl⟩ | h
    · rw [install_slot _ henc, install_slot _ henc]
    · exact absurd h ha

section seam
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e g7M) preF

end seam

end
end NearCubicWires.SourceConstruction.Bridge
end
