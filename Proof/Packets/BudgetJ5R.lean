import Proof.SourceAssembly.SourceSkelGen
import Proof.SourceAssembly.SourceStepsSelect

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceBudget
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## 1. The live scale and the classes at `rB` -/

/-- **The live scale at `rB`**: `L = rB + (rB + hT) + σ + 2`. -/
def liveOfR (hT : ParNat) : ParNat := fun sources gamma hg hh p =>
  SourceSteps.rBsel sources p + (SourceSteps.rBsel sources p + hT sources gamma hg hh p) + SelectedRuntime.sigma sources + 2

/-- **The ordered base class at `rB`**: divisor `4`, live scale `liveOfR hT`. -/
def SiteClassFam.orderedR (dS hT : ParNat)
    (hS : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ)
    (cP cT cS : ParCoef) : SiteClassFam where
  dS := dS
  hT := hT
  hS := fun sources gamma hg hh p => hS sources gamma hg hh p (liveOfR hT sources gamma hg hh p)
  m := fun _ _ _ _ _ => 4
  L := liveOfR hT
  cP := cP
  cT := cT
  cS := cS

/-- **The site class from a base class at `rB`** (`ofBase` with `rSel ↦ rB`). -/
def SiteClassFam.ofBaseR (B : SiteClassFam) : SiteClassFam where
  dS := fun sources gamma hg hh p => SourceSteps.rBsel sources p + B.dS sources gamma hg hh p
  hT := fun sources gamma hg hh p => SourceSteps.rBsel sources p + B.hT sources gamma hg hh p
  hS := fun sources gamma hg hh p => SourceSteps.rBsel sources p + B.hS sources gamma hg hh p
  m := B.m
  L := B.L
  cP := fun sources gamma hg hh p k => B.cP sources gamma hg hh p k +
    C10PartsSchedule.widthConst sources k^SourceSteps.rBsel sources p*
      (B.cP sources gamma hg hh p k + B.cP sources gamma hg hh p k + 4) + 4
  cT := fun sources gamma hg hh p k => B.cT sources gamma hg hh p k +
    C10PartsSchedule.widthConst sources k^SourceSteps.rBsel sources p*(B.cT sources gamma hg hh p k + B.cT sources gamma hg hh p k)
  cS := fun sources gamma hg hh p k => B.cS sources gamma hg hh p k +
    C10PartsSchedule.widthConst sources k^SourceSteps.rBsel sources p*(B.cS sources gamma hg hh p k + B.cS sources gamma hg hh p k)

/-! ## 2. The J5 free choices at `rB` -/

/-- **The recipe's source degree at `rB`** (`remDeg` with `rSel ↦ rB`). -/
def remDegR (Q : SiteClassFam) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : ℕ :=
  SourceSteps.rBsel sources p + (Q.dS sources gamma hg hh p + SourceSteps.rBsel sources p +
    reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources) +
    5*(SourceSteps.rBsel sources p + SourceSteps.rBsel sources p) +
    2*((SourceSteps.rBsel sources p + SourceSteps.rBsel sources p) + SourceSteps.rBsel sources p) +
    (SourceSteps.rBsel sources p + reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources)))

/-- The hierarchy index at `rB`. -/
abbrev kSelR (Q : SiteClassFam) (capIndex : ParNat)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  SourceParent.kOf capIndex (remDegR Q) sources gamma hg hh p

/-- The J5 constants at `rB`. -/
def constsOfR (Q : SiteClassFam) (capIndex : ParNat)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    J5Consts :=
  sourceConsts sources (kSelR Q capIndex sources gamma hg hh p) p (SourceSteps.rBsel sources p)
    (Q.dS sources gamma hg hh p) (Q.hT sources gamma hg hh p) (Q.hS sources gamma hg hh p)
    (Q.m sources gamma hg hh p) (Q.L sources gamma hg hh p)
    (Q.cP sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
    (Q.cT sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
    (Q.cS sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))

def j5FreeR (Q : SiteClassFam) (capIndex base : ParNat) : FreeChoices where
  capIndex := capIndex
  remainingDegree := remDegR Q
  r := fun sources _ _ _ p => SourceSteps.rBsel sources p
  base := base
  remainingFuel := fun sources gamma hg hh p n =>
    (constsOfR Q capIndex sources gamma hg hh p).fuel (CloseoutLanguage.selectedPCPP sources) n
      (C10PartsSchedule.widthAt sources (kSelR Q capIndex sources gamma hg hh p) n)
  remainingCoefficient := fun _ _ _ _ _ => 0
  remainingOnset := fun _ _ _ _ _ => 0
  tableCoefficient := fun _ _ _ _ _ => 0
  tableDegree := fun _ _ _ _ _ => 0

theorem j5FreeR_hr (Q : SiteClassFam) (capIndex base : ParNat) (sources : EightSources) (gamma : Real) (hg : 0 < gamma)
    (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (j5FreeR Q capIndex base).r sources gamma hg hh p =
      (SourceSteps.selR sources p (kOf (j5FreeR Q capIndex base).capIndex (j5FreeR Q capIndex base).remainingDegree
        sources gamma hg hh p)).exponent := rfl

def sfOfR (B : SiteClassFam) (capIndex : ParNat) : SiteFuelFam :=
  fun sources gamma hg hh p n _ _ _ =>
    siteRHS sources (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p) (SourceSteps.rBsel sources p)
      (B.dS sources gamma hg hh p) (B.hT sources gamma hg hh p) (B.hS sources gamma hg hh p)
      (B.m sources gamma hg hh p) (B.L sources gamma hg hh p)
      (B.cP sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
      (B.cT sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
      (B.cS sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p)) n
      (C10PartsSchedule.widthAt sources (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p) n)

/-- `sfOfR` is in `ofBaseR B`'s class (`site_inClasses`, `le_refl`). -/
theorem hsf_ofBaseR (B : SiteClassFam) (capIndex : ParNat)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (n : Nat) (x : BitInput n) (bits : List Bool) (ph : Phase) :
    Admission.InClasses ((SiteClassFam.ofBaseR B).dS sources gamma hg hh p) ((SiteClassFam.ofBaseR B).hT sources gamma hg hh p)
      ((SiteClassFam.ofBaseR B).hS sources gamma hg hh p) ((SiteClassFam.ofBaseR B).m sources gamma hg hh p)
      ((SiteClassFam.ofBaseR B).L sources gamma hg hh p) n
      (C10PartsSchedule.widthAt sources (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p) n)
      ((SiteClassFam.ofBaseR B).cP sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
      ((SiteClassFam.ofBaseR B).cT sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
      ((SiteClassFam.ofBaseR B).cS sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
      (sfOfR B capIndex sources gamma hg hh p n x bits ph) :=
  site_inClasses sources (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p) (SourceSteps.rBsel sources p)
    (B.dS sources gamma hg hh p) (B.hT sources gamma hg hh p) (B.hS sources gamma hg hh p)
    (B.m sources gamma hg hh p) (B.L sources gamma hg hh p)
    (B.cP sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
    (B.cT sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p))
    (B.cS sources gamma hg hh p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p)) n
    (C10PartsSchedule.widthAt sources (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p) n)

/-- **`base` at `rB`**: `selR`'s onset at the recipe's index, maxed with the admission onset `extra`. -/
def baseOfR (B : SiteClassFam) (capIndex extra : ParNat) : ParNat := fun sources gamma hg hh p =>
  max (SourceSteps.selR sources p (kSelR (SiteClassFam.ofBaseR B) capIndex sources gamma hg hh p)).onset
    (extra sources gamma hg hh p)

theorem hbase_ofR (B : SiteClassFam) (capIndex extra : ParNat) (sources : EightSources) (gamma : Real)
    (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    (SourceSteps.selR sources p
      (kOf (j5FreeR (SiteClassFam.ofBaseR B) capIndex (baseOfR B capIndex extra)).capIndex
        (j5FreeR (SiteClassFam.ofBaseR B) capIndex (baseOfR B capIndex extra)).remainingDegree sources gamma hg hh p)).onset ≤
      (j5FreeR (SiteClassFam.ofBaseR B) capIndex (baseOfR B capIndex extra)).base sources gamma hg hh p :=
  le_max_left _ _

/-- Every admission onset `extra` is below `base`. -/
theorem extra_le_baseR (B : SiteClassFam) (capIndex extra : ParNat) (sources : EightSources) (gamma : Real)
    (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    extra sources gamma hg hh p ≤ baseOfR B capIndex extra sources gamma hg hh p :=
  le_max_right _ _

abbrev fOrdGR (dS hT : ParNat) (hS cP cT cS : ParCoef) (den0 extra : ParNat) : FreeChoices :=
  j5FreeR (SiteClassFam.ofBaseR (SiteClassFam.orderedR dS hT hS cP cT cS)) (capIndexOf den0)
    (baseOfR (SiteClassFam.orderedR dS hT hS cP cT cS) (capIndexOf den0) extra)

abbrev sfOrdGR (dS hT : ParNat) (hS cP cT cS : ParCoef) (den0 : ParNat) : SiteFuelFam :=
  sfOfR (SiteClassFam.orderedR dS hT hS cP cT cS) (capIndexOf den0)

section j5
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

/-- **`fits` at `rB`**, from `hbase` and the site fuel in `Q`'s class (as `fitsG_of_site`, Selection `selR`). -/
theorem fitsGR_of_site (res : ResChoice) (Q : SiteClassFam) (capIndex base : ParNat)
    (code : SourceParent.CodeFamily mask selector packets rows (forcedChoices mask packets rows res (j5FreeR Q capIndex base)))
    (sf : SiteFuelFam)
    (hbase : ∀ sources gamma hg hh p, (SourceSteps.selR sources p
      (kOf (j5FreeR Q capIndex base).capIndex (j5FreeR Q capIndex base).remainingDegree sources gamma hg hh p)).onset ≤
        (j5FreeR Q capIndex base).base sources gamma hg hh p)
    (hsf : ∀ (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
      (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool) (ph : Phase),
      Admission.InClasses (Q.dS sources gamma hg hh p) (Q.hT sources gamma hg hh p)
        (Q.hS sources gamma hg hh p) (Q.m sources gamma hg hh p) (Q.L sources gamma hg hh p) n
        (C10PartsSchedule.widthAt sources (kSelR Q capIndex sources gamma hg hh p) n)
        (Q.cP sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
        (Q.cT sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
        (Q.cS sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
        (sf sources gamma hg hh p n x bits ph)) :
    FitsHoleG mask packets rows res (j5FreeR Q capIndex base) code sf := by
  intro sources gamma hg hh p n x bits ch C hn _
  have hS : (SourceSteps.selR sources p (kSelR Q capIndex sources gamma hg hh p)).onset ≤ n :=
    (hbase sources gamma hg hh p).trans ((base_le_onset sources p _ (Nat.succ_pos (capIndex sources gamma hg hh p))
      _).trans hn)
  exact fits_at sources p (capIndex sources gamma hg hh p + 1)
    (SourceSteps.selR sources p (kSelR Q capIndex sources gamma hg hh p)) hS x bits
    (sf sources gamma hg hh p n x bits) _ _ _ _ _ _ _ _ (hsf sources gamma hg hh p n x bits)

/-- **`split` at `rB`**: `2 ≤ m` and `rB + hT + σ + 2 ≤ L` (as `splitG_of_site`). -/
theorem splitGR_of_site (res : ResChoice) (Q : SiteClassFam) (capIndex base : ParNat)
    (code : SourceParent.CodeFamily mask selector packets rows (forcedChoices mask packets rows res (j5FreeR Q capIndex base)))
    (hm : ∀ sources gamma hg hh p, 2 ≤ Q.m sources gamma hg hh p)
    (horder : ∀ sources gamma hg hh p,
      SourceSteps.rBsel sources p + Q.hT sources gamma hg hh p + SelectedRuntime.sigma sources + 2 ≤ Q.L sources gamma hg hh p) :
    RuntimeShape.SplitRuntime (choicesOf (forcedChoices mask packets rows res (j5FreeR Q capIndex base)) code) := by
  refine splitRuntime_of_consts _ (constsOfR Q capIndex) ?_ (fun _ _ _ _ _ _ => rfl) hm ?_
  · intro sources gamma hg hh p
    exact (sourceConsts_degree _ _ _ _ _ _ _ _ _ _ _ _).symm
  · intro sources gamma hg hh p
    have h := horder sources gamma hg hh p
    have e := sourceConsts_tableExp sources (kSelR Q capIndex sources gamma hg hh p) p (SourceSteps.rBsel sources p)
      (Q.dS sources gamma hg hh p) (Q.hT sources gamma hg hh p) (Q.hS sources gamma hg hh p)
      (Q.m sources gamma hg hh p) (Q.L sources gamma hg hh p)
      (Q.cP sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
      (Q.cT sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
      (Q.cS sources gamma hg hh p (kSelR Q capIndex sources gamma hg hh p))
    show (constsOfR Q capIndex sources gamma hg hh p).tableExp + SelectedRuntime.sigma sources + 2 ≤
      (constsOfR Q capIndex sources gamma hg hh p).L
    unfold constsOfR
    rw [e]
    exact h

theorem fitsGR_ord (res : ResChoice) (dS hT : ParNat) (hS cP cT cS : ParCoef) (den0 extra : ParNat)
    (code : SourceParent.CodeFamily mask selector packets rows
      (forcedChoices mask packets rows res (fOrdGR dS hT hS cP cT cS den0 extra))) :
    FitsHoleG mask packets rows res (fOrdGR dS hT hS cP cT cS den0 extra) code (sfOrdGR dS hT hS cP cT cS den0) :=
  fitsGR_of_site mask packets rows res (SiteClassFam.ofBaseR (SiteClassFam.orderedR dS hT hS cP cT cS)) (capIndexOf den0)
    (baseOfR (SiteClassFam.orderedR dS hT hS cP cT cS) (capIndexOf den0) extra) code (sfOrdGR dS hT hS cP cT cS den0)
    (hbase_ofR (SiteClassFam.orderedR dS hT hS cP cT cS) (capIndexOf den0) extra)
    (fun sources gamma hg hh p n x bits ph =>
      hsf_ofBaseR (SiteClassFam.orderedR dS hT hS cP cT cS) (capIndexOf den0) sources gamma hg hh p n x bits ph)

theorem splitGR_ord (res : ResChoice) (dS hT : ParNat) (hS cP cT cS : ParCoef) (den0 extra : ParNat)
    (code : SourceParent.CodeFamily mask selector packets rows
      (forcedChoices mask packets rows res (fOrdGR dS hT hS cP cT cS den0 extra))) :
    RuntimeShape.SplitRuntime (choicesOf (forcedChoices mask packets rows res (fOrdGR dS hT hS cP cT cS den0 extra)) code) :=
  splitGR_of_site mask packets rows res (SiteClassFam.ofBaseR (SiteClassFam.orderedR dS hT hS cP cT cS)) (capIndexOf den0)
    (baseOfR (SiteClassFam.orderedR dS hT hS cP cT cS) (capIndexOf den0) extra) code
    (fun _ _ _ _ _ => by show 2 ≤ 4; omega)
    (fun _ _ _ _ _ => le_refl _)

end j5

end
end NearCubicWires.SourceBudget
end

