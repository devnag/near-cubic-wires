import Proof.SourceAssembly.AdmissionRuntime
import Proof.SourceAssembly.SourcePhaseSelect

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourcePhase
open NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section fuel
variable {dP hT hS m L n qn : Nat}

/-- **`hEntry`, moment/clause** (`entryFuel = 2*capacity a s + 4`), source-polynomial in the substituted request
size `s`, exactly as AD's `callBudget_inClasses`. -/
theorem entry_later_inClasses (a : RepairRepresentation.PointwisePCPPAlgorithm) (s sC sE : Nat)
    (hs : s + 1 ≤ sC*(n+1)^sE) (hd : sE*PCPPQueryCachedBounds.degree a ≤ dP) :
    Admission.InClasses dP hT hS m L n qn
      (2*PCPPQueryCachedBounds.coefficient a*sC^PCPPQueryCachedBounds.degree a + 4) 0 0
      (2*PCPPQueryCachedBounds.capacity a s + 4) := by
  unfold Admission.InClasses Admission.splitRHS PCPPQueryCachedBounds.capacity
  have h1 : (s+1)^PCPPQueryCachedBounds.degree a ≤
      sC^PCPPQueryCachedBounds.degree a*(n+1)^(sE*PCPPQueryCachedBounds.degree a) := by
    calc (s+1)^PCPPQueryCachedBounds.degree a ≤ (sC*(n+1)^sE)^PCPPQueryCachedBounds.degree a :=
          Nat.pow_le_pow_left hs _
      _ = sC^PCPPQueryCachedBounds.degree a*(n+1)^(sE*PCPPQueryCachedBounds.degree a) := by rw [mul_pow, ← pow_mul]
  have h2 : (n+1)^(sE*PCPPQueryCachedBounds.degree a) ≤ (n+1)^dP := Nat.pow_le_pow_right (by omega) hd
  have h3 : 1 ≤ (n+1)^dP := Nat.one_le_pow _ _ (by omega)
  have h4 : PCPPQueryCachedBounds.coefficient a*(s+1)^PCPPQueryCachedBounds.degree a ≤
      PCPPQueryCachedBounds.coefficient a*sC^PCPPQueryCachedBounds.degree a*(n+1)^dP := by
    calc PCPPQueryCachedBounds.coefficient a*(s+1)^PCPPQueryCachedBounds.degree a
        ≤ PCPPQueryCachedBounds.coefficient a*(sC^PCPPQueryCachedBounds.degree a*(n+1)^(sE*PCPPQueryCachedBounds.degree a)) :=
          Nat.mul_le_mul_left _ h1
      _ ≤ PCPPQueryCachedBounds.coefficient a*(sC^PCPPQueryCachedBounds.degree a*(n+1)^dP) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = PCPPQueryCachedBounds.coefficient a*sC^PCPPQueryCachedBounds.degree a*(n+1)^dP := by ring
  have e : (2*PCPPQueryCachedBounds.coefficient a*sC^PCPPQueryCachedBounds.degree a + 4)*(n+1)^dP =
      2*(PCPPQueryCachedBounds.coefficient a*sC^PCPPQueryCachedBounds.degree a*(n+1)^dP) + 4*(n+1)^dP := by ring
  simp only [Nat.zero_mul, Nat.add_zero]
  omega

/-- The same at the actual cache capacity `capC` of the phase entry. -/
theorem entry_later_inClasses_capC (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (sC sE : Nat)
    (hs : (req sources k clock x oracle).circuit.size + (req sources k clock x oracle).arity + 1 ≤ sC*(n+1)^sE)
    (hd : sE*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources) ≤ dP) :
    Admission.InClasses dP hT hS m L n qn
      (2*PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP sources)*
        sC^PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources) + 4) 0 0
      (2*capC sources k clock x oracle + 4) :=
  entry_later_inClasses _ _ sC sE hs hd

end fuel

/-! ## The fold widths -/

/-- The schedule width `b` is polynomial once the PCP width is. -/
theorem b_poly (sources : EightSources) (k r n wC wE : Nat)
    (hw : C10PartsSchedule.widthAt sources k n + 1 ≤ wC*(n+1)^wE) :
    C10PartsSchedule.entryWidthSchedule sources k r n + 1 ≤
      (C10PartsSchedule.thresholdFloor sources + 1 + wC^r)*(n+1)^(wE*r) := by
  unfold C10PartsSchedule.entryWidthSchedule C10PartsSchedule.widthPower
  have h1 : (C10PartsSchedule.widthAt sources k n + 1)^r ≤ wC^r*(n+1)^(wE*r) := by
    calc (C10PartsSchedule.widthAt sources k n + 1)^r ≤ (wC*(n+1)^wE)^r := Nat.pow_le_pow_left hw r
      _ = wC^r*(n+1)^(wE*r) := by rw [mul_pow, ← pow_mul]
  have h3 : 1 ≤ (n+1)^(wE*r) := Nat.one_le_pow _ _ (by omega)
  have h4 : C10PartsSchedule.thresholdFloor sources + 1 ≤ (C10PartsSchedule.thresholdFloor sources + 1)*(n+1)^(wE*r) :=
    Nat.le_mul_of_pos_right _ h3
  have e : (C10PartsSchedule.thresholdFloor sources + 1 + wC^r)*(n+1)^(wE*r) =
      (C10PartsSchedule.thresholdFloor sources + 1)*(n+1)^(wE*r) + wC^r*(n+1)^(wE*r) := by ring
  omega

section counts
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {b : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}

/-- A phase's record count IS its polynomial's monomial count (per-clause `_hlen`, D1's permutation). -/
theorem loop_entries_length (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph b code) :
    L.entries.length = (Poly sources p k den clock n x oracle bits ph).monomials.length := by
  have h1 : L.entries.length = (loopOrder L).length := by
    unfold ClauseLoop.entries loopOrder
    rw [List.length_flatten, List.length_flatten, List.map_ofFn, List.map_ofFn]
    congr 1
    congr 1
    funext c
    exact (L.trace c)._hlen
  rw [h1]
  exact (loop_horder L).length_eq.symm

/-- The phase polynomial has at most (clauses) × (calls per clause) monomials. -/
theorem poly_length_le (K : Nat)
    (hK : ∀ c, (CloseoutFinalC10SupplierCalls.siteCalls ph (pcppAt sources k clock x oracle)
      (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) C10TotalDecode.Atom.systematic c).monomials.length ≤ K) :
    (Poly sources p k den clock n x oracle bits ph).monomials.length ≤ NC sources k clock x oracle * K := by
  rw [(phase_monomials_perm ph (pcppAt sources k clock x oracle)
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) C10TotalDecode.Atom.systematic).length_eq,
    List.length_flatten, List.map_ofFn]
  have h := List.sum_le_card_nsmul (List.ofFn (List.length ∘ fun ci =>
    (CloseoutFinalC10SupplierCalls.siteCalls ph (pcppAt sources k clock x oracle)
      (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) C10TotalDecode.Atom.systematic ci).monomials)) K
    (by
      intro y hy
      obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hy
      exact hK c)
  rw [List.length_ofFn, smul_eq_mul] at h
  exact h

end counts

/-- **`hW`** for AD's `branchFuel_of_phases`, from the three phase width bounds. -/
theorem widths_hW (width : Phase → Nat) (n wC wE : Nat) (h : ∀ ph, width ph + 1 ≤ wC*(n+1)^wE) :
    max (width .penalty) (max (width .moment) (width .clause)) + 1 ≤ wC*(n+1)^wE := by
  have h1 := h .penalty
  have h2 := h .moment
  have h3 := h .clause
  omega

/-! ## Hypothesis-free forms: the PCP width is logarithmic, the fold fuel is quintic -/

theorem two_pow_ge : ∀ n : Nat, n + 2 ≤ 2 ^ (n+1)
  | 0 => by norm_num
  | n+1 => by
    have := two_pow_ge n
    rw [pow_succ]
    omega

theorem logScale_le_succ (n : Nat) : logScale n ≤ n + 1 := by
  unfold logScale
  exact Nat.clog_le_of_le_pow (two_pow_ge n)

theorem widthAt_poly (sources : EightSources) (k n : Nat) :
    C10PartsSchedule.widthAt sources k n + 1 ≤ C10PartsSchedule.widthConst sources k * (n+1)^1 := by
  rw [pow_one]
  exact (C10PartsSchedule.widthAt_succ_le sources k n).trans
    (Nat.mul_le_mul_left _ (logScale_le_succ n))

theorem foldFuel_le (b count : Nat) :
    CloseoutFinalC10RetainedPhaseFold.fuel b count ≤ 3800000*(b+count+1)^5 := by
  have hw := C10LedgerBounds.wordsFuel_le b count
  have hd := C10LedgerBounds.dockedFuel_le
    (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel (CloseoutFinalC10WorkerDock.joinScalarWidth b count)) b count 0
  have he := C10PartsSchedule.emitFuel_le (CloseoutFinalC10WorkerDock.joinScalarWidth b count)
  have hj := C10PartsSchedule.join_succ_le b count
  have h1 : 1 ≤ b+count+1 := by omega
  have h24 : (b+count+1)^2 ≤ (b+count+1)^5 := Nat.pow_le_pow_right h1 (by norm_num)
  have h45 : (b+count+1)^4 ≤ (b+count+1)^5 := Nat.pow_le_pow_right h1 (by norm_num)
  have h05 : 1 ≤ (b+count+1)^5 := Nat.one_le_pow _ _ (by omega)
  unfold CloseoutFinalC10RetainedPhaseFold.fuel
  omega

/-- **The fold fuel in the classes**, from a polynomial bound on `b + count + 1`. -/
theorem foldFuel_inClasses {dP hT hS m L n qn : Nat} (b count xC xE : Nat)
    (hx : b + count + 1 ≤ xC*(n+1)^xE) (hd : 5*xE ≤ dP) :
    Admission.InClasses dP hT hS m L n qn (3800000*xC^5) 0 0 (CloseoutFinalC10RetainedPhaseFold.fuel b count) := by
  unfold Admission.InClasses Admission.splitRHS
  have h1 := foldFuel_le b count
  have h2 : (b+count+1)^5 ≤ xC^5*(n+1)^(xE*5) := by
    calc (b+count+1)^5 ≤ (xC*(n+1)^xE)^5 := Nat.pow_le_pow_left hx 5
      _ = xC^5*(n+1)^(xE*5) := by rw [mul_pow, ← pow_mul]
  have h3 : xC^5*(n+1)^(xE*5) ≤ xC^5*(n+1)^dP := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have e : 3800000*xC^5*(n+1)^dP = 3800000*(xC^5*(n+1)^dP) := by ring
  simp only [Nat.zero_mul, Nat.add_zero]
  omega

end
end NearCubicWires.SourcePhase
end
