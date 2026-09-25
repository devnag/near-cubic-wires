import Proof.SourceAssembly.SourceFactorSelYbFit
import Proof.SourceAssembly.SourceRequestSelCoefV
import Proof.SourceAssembly.SourceRequestSelDWin
import Proof.SourceAssembly.SourceRequestSelWinCore

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
namespace NearCubicWires.SourceRequest.SelWinSite
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
open NearCubicWires.SourceRequest.SelWinCore
open NearCubicWires.SourceRequest.SelG7Spec (g7costW)
open NearCubicWires.PolynomialSchedule
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes P1TopDown.WorkspaceSelectedAdmission.originalTapes
  P1TopDown.WorkspaceSelectedEntry.size RepairSource.SelectedRecoveryIntegration.outer

/-! ## 1. The `q`-bound -/

section poly
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)

/-- The coefficient value bound's polynomial (`VbF n ≤ vbv (widthAt k n)`). -/
def vbv (q : Nat) : Nat :=
  2 * max 1 (RepairSource.CloseoutXor.cap (RepairSource.CompetitorRationalGap.zeta (RepairSource.CloseoutFinal.constantsOf sources))
      (CloseoutFinalC10ModeNativeSchedule.sampleAt sources p q) p.copies
    * max 1 (2 * CloseoutFinalC10ModeNativeSchedule.clauseAt sources p q)) + 4

theorem sampleAt_poly : PolynomiallyBounded (CloseoutFinalC10ModeNativeSchedule.sampleAt sources p) := by
  have h1 := polynomiallyBounded_constant 1
  have ha : PolynomiallyBounded (CloseoutFinalC10ModeNativeWidth.arityAt sources) :=
    polynomiallyBounded_max polynomiallyBounded_id
      (polynomiallyBounded_constant (RepairSource.CloseoutLanguage.selectedPCPP sources).minimumArity)
  have hr : PolynomiallyBounded (RepairSource.CloseoutLanguage.clauseWidth p.clauseDegree) :=
    polynomiallyBounded_mono (RepairSource.CloseoutLanguage.clause_linear p.clauseDegree)
      (polynomiallyBounded_mul (polynomiallyBounded_constant p.clauseDegree)
        (polynomiallyBounded_add polynomiallyBounded_id h1))
  exact polynomiallyBounded_add (polynomiallyBounded_add ha hr) h1

theorem clauseAt_poly : PolynomiallyBounded (CloseoutFinalC10ModeNativeSchedule.clauseAt sources p) :=
  RepairSource.CloseoutSourceCounts.shortBound_polynomial _ _ _ _

theorem vbv_poly : PolynomiallyBounded (vbv sources p) := by
  have h1 := polynomiallyBounded_constant 1
  have h2 := polynomiallyBounded_constant 2
  have hcap : PolynomiallyBounded (fun q => RepairSource.CloseoutXor.cap
      (RepairSource.CompetitorRationalGap.zeta (RepairSource.CloseoutFinal.constantsOf sources))
      (CloseoutFinalC10ModeNativeSchedule.sampleAt sources p q) p.copies) :=
    polynomiallyBounded_mul
      (polynomiallyBounded_mul (polynomiallyBounded_constant 32) (polynomiallyBounded_add (sampleAt_poly sources p) h1))
      (polynomiallyBounded_constant ((RepairSource.CompetitorRationalGap.zeta (RepairSource.CloseoutFinal.constantsOf sources)).den ^
        (3 * p.copies + 2)))
  exact polynomiallyBounded_add (polynomiallyBounded_mul h2 (polynomiallyBounded_max h1
    (polynomiallyBounded_mul hcap (polynomiallyBounded_max h1 (polynomiallyBounded_mul h2 (clauseAt_poly sources p))))))
    (polynomiallyBounded_constant 4)

theorem termAt_poly : PolynomiallyBounded (CloseoutFinalC10ModeNativeSchedule.termAt sources p) :=
  polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (clauseAt_poly sources p))
    (polynomiallyBounded_comp (RepairSource.CloseoutWitnessResources.xor_terms_polynomial
      (RepairSource.CompetitorRationalGap.zeta (RepairSource.CloseoutFinal.constantsOf sources)) p.copies) (sampleAt_poly sources p))

end poly

section sq
variable (selector : CyclicChoice.Laws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (Ccw Dcw CD DD r L target degree tg : Nat)

def ybv (q : Nat) : Nat :=
  (SourceBudget.Params.inC0 (decompositionOf sources) degree tg + 4 * L) *
      (q + 1) ^ SourceBudget.Params.inE0 (decompositionOf sources) degree tg +
    2 * (SourceBudget.betaC (decompositionOf sources) degree * (q + 1) ^ SourceBudget.betaE (decompositionOf sources) degree) +
    (40 * NearCubicWires.SourceStart.MetaCost.Sz selector sources p packets L q + 200) + 1

/-- **Every `q`-sized quantity of the call, at once.** -/
def sqv (q : Nat) : Nat :=
  PCPPQueryCachedBounds.capacity (RepairSource.CloseoutLanguage.selectedPCPP sources)
      (2 * (SourceBudget.reqC sources p * (q + 1) ^ SourceBudget.reqE sources p)) +
    2 * CloseoutFinalC10ModeNativeSchedule.termAt sources p q + Ccw * (q + 1) ^ Dcw + CD * (q + 1) ^ DD + L + target +
    (C10PartsSchedule.thresholdFloor sources + 1) * (q + 1) ^ r + vbv sources p q +
    ybv selector sources p packets L degree tg q + 4

theorem ybv_poly : PolynomiallyBounded (ybv selector sources p packets L degree tg) := by
  unfold ybv
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_mul (polynomiallyBounded_constant _)
      (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) _))
    (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (polynomiallyBounded_mul (polynomiallyBounded_constant _)
      (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) _))))
    (polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 40)
      (NearCubicWires.SourceStart.MetaCost.Sz_poly selector sources p packets L)) (polynomiallyBounded_constant 200)))
    (polynomiallyBounded_constant 1)

theorem sqv_poly : PolynomiallyBounded (sqv selector sources p packets Ccw Dcw CD DD r L target degree tg) := by
  have hp1 : PolynomiallyBounded (fun q : Nat => q + 1) :=
    polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)
  have hcw : ∀ c d : Nat, PolynomiallyBounded (fun q : Nat => c * (q + 1) ^ d) := fun c d =>
    polynomiallyBounded_mul (polynomiallyBounded_constant c) (polynomiallyBounded_pow hp1 d)
  have hcap : PolynomiallyBounded (fun q => PCPPQueryCachedBounds.capacity (RepairSource.CloseoutLanguage.selectedPCPP sources)
      (2 * (SourceBudget.reqC sources p * (q + 1) ^ SourceBudget.reqE sources p))) := by
    have hin : PolynomiallyBounded (fun q : Nat => 2 * (SourceBudget.reqC sources p * (q + 1) ^ SourceBudget.reqE sources p)) :=
      polynomiallyBounded_mul (polynomiallyBounded_constant 2) (hcw _ _)
    have hout : PolynomiallyBounded (PCPPQueryCachedBounds.capacity (RepairSource.CloseoutLanguage.selectedPCPP sources)) := by
      unfold PCPPQueryCachedBounds.capacity
      exact hcw _ _
    exact polynomiallyBounded_comp hout hin
  unfold sqv
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_add hcap (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (termAt_poly sources p)))
      (hcw Ccw Dcw)) (hcw CD DD)) (polynomiallyBounded_constant L)) (polynomiallyBounded_constant target))
      (hcw _ r)) (vbv_poly sources p)) (ybv_poly selector sources p packets L degree tg)) (polynomiallyBounded_constant 4)

/-- The summands of `sqv` are below it. -/
theorem sqv_ge (q : Nat) :
    PCPPQueryCachedBounds.capacity (RepairSource.CloseoutLanguage.selectedPCPP sources)
        (2 * (SourceBudget.reqC sources p * (q + 1) ^ SourceBudget.reqE sources p)) ≤
      sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    2 * CloseoutFinalC10ModeNativeSchedule.termAt sources p q + 4 ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    Ccw * (q + 1) ^ Dcw ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    CD * (q + 1) ^ DD ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    L ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    target ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    (C10PartsSchedule.thresholdFloor sources + 1) * (q + 1) ^ r ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    vbv sources p q ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    ybv selector sources p packets L degree tg q ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q ∧
    4 ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q := by
  unfold sqv
  omega

/-- The `q`-part as one polynomial. -/
theorem qpart_poly (wC wE : Nat) :
    PolynomiallyBounded (fun q => 2 * (2 ^ 200 * (sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q + 1) ^ 25 +
      wC * (sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q + 1) ^ wE)) := by
  have hs := polynomiallyBounded_add (sqv_poly selector sources p packets Ccw Dcw CD DD r L target degree tg)
    (polynomiallyBounded_constant 1)
  exact polynomiallyBounded_mul (polynomiallyBounded_constant 2) (polynomiallyBounded_add
    (polynomiallyBounded_mul (polynomiallyBounded_constant _) (polynomiallyBounded_pow hs 25))
    (polynomiallyBounded_mul (polynomiallyBounded_constant _) (polynomiallyBounded_pow hs wE)))

/-- **The onset**: past it, `Ebd … ≤ tableClass L 0 q` at `q = widthAt k n`, for the site's `k` with `max 25 dL + 1 ≤ k + 2`. -/
theorem onset_exists (k cL dL wC wE : Nat) (hk : max 25 dL + 1 ≤ k + 2) :
    ∃ o, ∀ n, o ≤ n →
      Ebd n (sqv selector sources p packets Ccw Dcw CD DD r L target degree tg (C10PartsSchedule.widthAt sources k n)) cL dL wC wE ≤
        RuntimeShape.tableClass L 0 (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨n0, h0⟩ := SourceBudget.npoly_le_twoPow_res sources k (2 * (2 ^ 200 + cL)) (max 25 dL) L hk
  obtain ⟨q0, hq0⟩ := SourceBudget.polyBounded_le_Rc _ (qpart_poly selector sources p packets Ccw Dcw CD DD r L target degree tg wC wE) L
  obtain ⟨n1, h1⟩ := SourceBudget.widthAt_ge_eventually sources k q0
  refine ⟨max n0 n1, fun n hn => ?_⟩
  set q := C10PartsSchedule.widthAt sources k n with hq
  have hN := h0 n (le_trans (le_max_left _ _) hn)
  have hQ := hq0 q (h1 n (le_trans (le_max_right _ _) hn)) 1 0 (le_refl 1)
  have ht : RuntimeShape.tableClass L 0 q = 2 ^ (q - normalizedLiveCount q L) := by
    unfold RuntimeShape.tableClass; simp
  rw [one_mul] at hQ
  have hd1 : (n + 1) ^ 25 ≤ (n + 1) ^ (max 25 dL) := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hd2 : (n + 1) ^ dL ≤ (n + 1) ^ (max 25 dL) := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have hNp : 2 * (2 ^ 200 * (n + 1) ^ 25 + cL * (n + 1) ^ dL) ≤ 2 * (2 ^ 200 + cL) * (n + 1) ^ (max 25 dL) := by
    have e : 2 * (2 ^ 200 + cL) * (n + 1) ^ (max 25 dL) =
        2 * (2 ^ 200 * (n + 1) ^ (max 25 dL) + cL * (n + 1) ^ (max 25 dL)) := by ring
    rw [e]
    exact Nat.mul_le_mul_left 2 (Nat.add_le_add (Nat.mul_le_mul_left _ hd1) (Nat.mul_le_mul_left _ hd2))
  rw [ht]
  exact Ebd_le _ _ _ _ _ _ _ (hNp.trans hN) (by rw [← ht]; exact hQ)

end sq

/-! ## 2. The instance's size facts -/

section inst
variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n ^ (k + 2))) {gamma : Real}
  (p : Parameters sources gamma) (den : Nat) {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((RepairSource.SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
  (bits : List Bool)

/-- Every coordinate's monomial count is below the capped decoder's term cap. -/
theorem coord_len_le (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).monomials.length ≤
      (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).termCap := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [PCJd04de0277f804fcc_.coordinate_sym sources k clock p den x oracle bits hs j]
    exact (CloseoutFinalC10ClauseBitsUniform.mapPolynomial_monomials_length _ _).trans_le
      (CloseoutFinalC10ClauseBitsUniform.familyCoordinate_monomials_length_le rfl
        (P1Independent.CappedDecode.symFamilyOf sources k clock p den x oracle bits) j)
  · rw [PCJd04de0277f804fcc_.coordinate_thr sources k clock p den x oracle bits hs j]
    have ht : (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle).termCap =
        (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).termCap := rfl
    rw [← ht]
    exact (CloseoutFinalC10ClauseBitsUniform.mapPolynomial_monomials_length _ _).trans_le
      (CloseoutFinalC10ClauseBitsUniform.familyCoordinate_monomials_length_le rfl
        (P1Independent.CappedDecode.thrFamilyOf sources k clock p den x oracle bits) j)

end inst

section site
variable (sources : EightSources) (k : Nat) {gamma : Real} (p : Parameters sources gamma) (den n : Nat) (x : BitInput n)
  (bits : List Bool)

theorem coord_len_site (j : Fin (CloseoutWitnessPolicy.variableCount sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) :
    (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits j).monomials.length ≤
      CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n) :=
  (coord_len_le sources k _ p den x _ bits j).trans
    (CloseoutFinalC10ClauseBitsUniform.termCap_le sources k p n x bits)

/-- The call's cache capacity is below the site polynomial's first term. -/
theorem cap_le_site :
    PCPPQueryCachedBounds.capacity (RepairSource.CloseoutLanguage.selectedPCPP sources)
        ((req sources k (PolynomialClock.ordinaryClock k) x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size +
        (req sources k (PolynomialClock.ordinaryClock k) x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity) ≤
      PCPPQueryCachedBounds.capacity (RepairSource.CloseoutLanguage.selectedPCPP sources)
        (2 * (SourceBudget.reqC sources p * (C10PartsSchedule.widthAt sources k n + 1) ^ SourceBudget.reqE sources p)) := by
  have h1 := SourceBudget.req_size_le sources k p x bits
  have h2 := SourceBudget.shortAt_le sources p (C10PartsSchedule.widthAt sources k n)
  unfold PCPPQueryCachedBounds.capacity
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- The record width `b` is below `(thresholdFloor + 1)·(q+1)^r`. -/
theorem b_le_site (r : Nat) :
    C10PartsSchedule.entryWidthSchedule sources k r n ≤
      (C10PartsSchedule.thresholdFloor sources + 1) * (C10PartsSchedule.widthAt sources k n + 1) ^ r := by
  unfold C10PartsSchedule.entryWidthSchedule C10PartsSchedule.widthPower
  have h2 : 1 ≤ (C10PartsSchedule.widthAt sources k n + 1) ^ r := Nat.one_le_pow _ _ (by omega)
  have e : (C10PartsSchedule.thresholdFloor sources + 1) * (C10PartsSchedule.widthAt sources k n + 1) ^ r =
      C10PartsSchedule.thresholdFloor sources * (C10PartsSchedule.widthAt sources k n + 1) ^ r +
        (C10PartsSchedule.widthAt sources k n + 1) ^ r := by ring
  have h3 : C10PartsSchedule.thresholdFloor sources ≤
      C10PartsSchedule.thresholdFloor sources * (C10PartsSchedule.widthAt sources k n + 1) ^ r :=
    Nat.le_mul_of_pos_right _ h2
  omega

/-- `VbF n ≤ vbv (widthAt k n)` (`SelCoefV.VbF_le`). -/
theorem vb_le_site : SelCoefV.VbF sources k p n ≤ vbv sources p (C10PartsSchedule.widthAt sources k n) :=
  SelCoefV.VbF_le sources k p n

end site

section v5
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p

abbrev sqS (L target tg q : Nat) : Nat :=
  sqv selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg q

/-- `1 ≤ cwC` (the coefficient of a PolynomiallyBounded witness is positive). -/
theorem cwC_pos : 0 < NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p := by
  unfold NearCubicWires.SourceSkeleton.Params.cwC
  exact (Classical.choose_spec (Classical.choose_spec (CloseoutFinalC10ModeNativeSchedule.jointCap_polynomial sources p))).1

end v5

end
end NearCubicWires.SourceRequest.SelWinSite
end
