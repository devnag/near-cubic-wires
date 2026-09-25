import Proof.SourceAssembly.SourcePhaseCoeff

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope
open NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.ComponentwiseCircuitRestriction NearCubicWires.RecoveryWitnessPolicy
namespace NearCubicWires.SourcePhase
open NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section generic

theorem pop_le {Circuit Gate : Type} (occ : Circuit → List Gate)
    (circuits : List Circuit) (wireCap : Nat)
    (h : ∀ circuit ∈ circuits, (occ circuit).length ≤ wireCap) :
    (circuits.flatMap occ).length ≤ circuits.length * wireCap := by
  induction circuits with
  | nil => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, one_mul]
    have ht := ih (fun circuit hc => h circuit (by simp [hc]))
    have hh := h head (by simp)
    omega

theorem sym_den_le (L target : Nat) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (wireCap : Nat) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ circuit ∈ r.circuits, circuit.wireCount ≤ wireCap) :
    LiveRows.symDenominator r L target ≤ 2 ^ (r.q + symSeedBits wireCap target) := by
  have hpop : (symmetricFourfoldOccurrences r).length ≤ 4 * wireCap :=
    (pop_le symmetricCircuitOccurrences r.circuits wireCap
      (fun circuit hc => (symmetricCircuitOccurrences_length_le circuit).trans
        (hw circuit hc))).trans (Nat.mul_le_mul_right wireCap hfour)
  have hseed := walkExponent_le_seedEnvelope (denominator := symmetricListDenominator r target)
    hpop ((touchingCost_le_length _ (CyclicChoice.live (symmetricFourfoldOccurrences r) L)).trans hpop)
    (Nat.mul_le_mul_right (target + 1) hfour)
  unfold LiveRows.symDenominator LiveRows.Seed LiveRows.bound
  rw [card_walkSample, ← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  unfold symSeedBits
  omega

theorem thr_den_le (a : DecompositionAlgorithm) (L target : Nat)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (wireCap descCap : Nat) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ circuit ∈ r.circuits, circuit.wireCount ≤ wireCap)
    (hd : ∀ circuit ∈ r.circuits, circuit.descriptionBits ≤ descCap) :
    LiveRows.thrDenominator a r L target ≤ 2 ^ (r.q + thrSeedBits a wireCap descCap target) := by
  have hpop : (thresholdFourfoldOccurrences r).length ≤ 4 * wireCap :=
    (pop_le thresholdCircuitOccurrences r.circuits wireCap
      (fun circuit hc => (thresholdCircuitOccurrences_length_le circuit).trans
        (hw circuit hc))).trans (Nat.mul_le_mul_right wireCap hfour)
  have hp : Fintype.card (PrimeIndex (primeCutoff a r target)) ≤
      2 ^ Nat.clog 2 (tupleCutoffBound a descCap target + 1) := by
    rw [Fintype.card_coe]
    exact (primesUpTo_primeCutoff_card_le _ r descCap target hfour hd).trans
      (Nat.le_pow_clog (by decide) _)
  have hs : Fintype.card (LiveRows.Seed (thresholdFourfoldOccurrences r)
      (CyclicChoice.live (thresholdFourfoldOccurrences r) L) (listDenominator a r target)) ≤
      2 ^ seedEnvelope (4 * wireCap) (4 * wireCap) (tupleListDenominatorBound a descCap target) := by
    unfold LiveRows.Seed LiveRows.bound
    rw [card_walkSample]
    exact Nat.pow_le_pow_right (by decide)
      (walkExponent_le_seedEnvelope hpop ((touchingCost_le_length _ _).trans hpop)
        (listDenominator_le _ r descCap target hfour hd))
  unfold LiveRows.thrDenominator
  apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul hp hs)).trans_eq
  unfold thrSeedBits
  rw [← pow_add, ← pow_add, Nat.add_comm]

/-- The capped wire scale is at most the uncapped one. -/
theorem floor_capped_le (den e w : Nat) :
    ⌊wireScale (1 / (den : Real)) e w⌋₊ ≤ ⌊wireScale 1 e w⌋₊ := by
  apply Nat.floor_mono
  unfold wireScale
  have hone : 1 / (den : Real) ≤ 1 := by
    rcases Nat.eq_zero_or_pos den with h | h
    · subst h; simp
    · rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast h
  have hw : (0 : Real) ≤ (w : Real) ^ 3 := by positivity
  have hl : (0 : Real) ≤ (logScale w : Real) ^ e := by positivity
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hone hw) hl

theorem tdc_mono {a w w' : Nat} (h : w ≤ w') :
    thresholdDescriptionCap a w ≤ thresholdDescriptionCap a w' := by
  unfold thresholdDescriptionCap
  exact Nat.add_le_add (normalizedGateDescriptionCap_mono h) (Nat.mul_le_mul_right _ h)

theorem rtdc_mono {core t c c' : Nat} (h : c ≤ c') :
    restrictedThresholdDescriptionCap core t (2 ^ c) c ≤
      restrictedThresholdDescriptionCap core t (2 ^ c') c' := by
  unfold restrictedThresholdDescriptionCap restrictedGateDescriptionCap restrictedParameterBound
  have hp : 2 ^ c ≤ 2 ^ c' := Nat.pow_le_pow_right (by decide) h
  have hb : natBitLength ((t + 1) * 2 ^ c) ≤ natBitLength ((t + 1) * 2 ^ c') := by
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left _ hp)) 1
  have hm := Nat.mul_le_mul_left (core + 1) hb
  exact Nat.mul_le_mul (by omega) (by omega)

end generic

section capped
variable (sources : EightSources) (k : Nat) {gamma : Real} (p : Parameters sources gamma) (den : Nat)
  {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n))
  (bits : List Bool)

theorem capped_desc_le :
    (P1Independent.CappedDecode.thrLimits sources k (PolynomialClock.ordinaryClock k) p den x oracle).descriptionCap ≤
      carriedDescCap sources k p n :=
  rtdc_mono (tdc_mono (floor_capped_le den 9 _))

theorem capped_coord_wires (j : Fin (CloseoutWitnessPolicy.variableCount sources k (PolynomialClock.ordinaryClock k) x oracle)) :
    (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracle bits j).FactorsSatisfy
      (fun atom => atomWires atom ≤ C10SiteWireEnvelope.envelopeCap sources k n) := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [PCJd04de0277f804fcc_.coordinate_sym sources k _ p den x oracle bits hs j]
    refine C10SiteWireEnvelope.mapPolynomial_factorsSatisfy _ _ _ ?_
    refine C10SiteWireEnvelope.FactorsSatisfy.mono (C10SiteWireEnvelope.familyCoordinate_factorsSatisfy_wires rfl
      (P1Independent.CappedDecode.symFamilyOf sources k _ p den x oracle bits) j) ?_
    intro atom hatom
    have hcap : (P1Independent.CappedDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p den x oracle).wireCap ≤
        C10SiteWireEnvelope.envelopeCap sources k n := by
      unfold C10SiteWireEnvelope.envelopeCap
      exact le_trans (floor_capped_le den 5 _) (le_trans (le_max_left _ _) (le_max_right _ _))
    exact le_trans hatom hcap
  · rw [PCJd04de0277f804fcc_.coordinate_thr sources k _ p den x oracle bits hs j]
    refine C10SiteWireEnvelope.mapPolynomial_factorsSatisfy _ _ _ ?_
    refine C10SiteWireEnvelope.FactorsSatisfy.mono (C10SiteWireEnvelope.familyCoordinate_factorsSatisfy_wires rfl
      (P1Independent.CappedDecode.thrFamilyOf sources k _ p den x oracle bits) j) ?_
    intro atom hatom
    have hcap : (P1Independent.CappedDecode.thrLimits sources k (PolynomialClock.ordinaryClock k) p den x oracle).wireCap ≤
        C10SiteWireEnvelope.envelopeCap sources k n := by
      unfold C10SiteWireEnvelope.envelopeCap
      exact le_trans (floor_capped_le den 9 _) (le_trans (le_max_right _ _) (le_max_right _ _))
    exact le_trans hatom hcap

theorem capped_coord_desc (j : Fin (CloseoutWitnessPolicy.variableCount sources k (PolynomialClock.ordinaryClock k) x oracle)) :
    (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracle bits j).FactorsSatisfy
      (CarriedDescription (carriedDescCap sources k p n)) := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [PCJd04de0277f804fcc_.coordinate_sym sources k _ p den x oracle bits hs j]
    refine C10SiteWireEnvelope.mapPolynomial_factorsSatisfy _ _ _ ?_
    intro monomial hmonomial atom hatom
    trivial
  · rw [PCJd04de0277f804fcc_.coordinate_thr sources k _ p den x oracle bits hs j]
    refine C10SiteWireEnvelope.mapPolynomial_factorsSatisfy _ _ _ ?_
    refine C10SiteWireEnvelope.FactorsSatisfy.mono (familyCoordinate_description rfl
      (P1Independent.CappedDecode.thrFamilyOf sources k _ p den x oracle bits) j) ?_
    intro atom hatom
    exact le_trans hatom (capped_desc_le sources k p den x oracle)

/-- **D7 at one call**: every record denominator of a capped clause's calls is at most `2^nativeDenBits`. -/
theorem fraction_den_le (liveScale : Nat) (ph : Phase)
    (address : Fin (2 ^ (pcppAt sources k (PolynomialClock.ordinaryClock k) x oracle).clauseBits))
    (m : CircuitMonomial (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x oracle)) 4)
    (hmem : m ∈ (CloseoutFinalC10SupplierCalls.siteCalls ph (pcppAt sources k (PolynomialClock.ordinaryClock k) x oracle)
      (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracle bits)
      C10TotalDecode.Atom.systematic address).monomials) :
    (LiveRows.fraction sources liveScale
      (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
      (CloseoutWitness.BoundedFields.symmetric bits) m.factors).2 ≤ 2 ^ nativeDenBits sources k p n := by
  have hm := site_mode sources p k den (PolynomialClock.ordinaryClock k) x oracle bits ph address m hmem
  have hw := C10SiteWireEnvelope.siteCalls_factorsSatisfy ph _ _ C10TotalDecode.Atom.systematic _
    (capped_coord_wires sources k p den x oracle bits)
    (fun i => le_trans (C10SiteWireEnvelope.atomWires_systematic_le _ i) (le_max_left _ _)) address m hmem
  have hd := C10SiteWireEnvelope.siteCalls_factorsSatisfy ph _ _ C10TotalDecode.Atom.systematic _
    (capped_coord_desc sources k p den x oracle bits) (fun _ => trivial) address m hmem
  have hfourS : (m.factors.map C10NaturalModeAtoms.nativeSymmetricAtom).length ≤ 4 := by
    rw [List.length_map]
    exact m.degree_le
  have hfourT : (m.factors.map C10NaturalModeAtoms.nativeThresholdAtom).length ≤ 4 := by
    rw [List.length_map]
    exact m.degree_le
  cases hs : CloseoutWitness.BoundedFields.symmetric bits
  · rw [hs] at hm
    have hbound := thr_den_le (decompositionOf sources) liveScale
      (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
      ⟨_, m.factors.map C10NaturalModeAtoms.nativeThresholdAtom⟩
      (nativeWireCap sources k n) (nativeDescCap sources k p n) hfourT
      (by
        intro circuit hc
        obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hc
        exact nativeThreshold_wire atom (hm atom ha) _ (hw atom ha))
      (by
        intro circuit hc
        obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hc
        exact nativeThreshold_description atom (hm atom ha) _ (hd atom ha))
    exact hbound.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (le_max_right _ _) _))
  · rw [hs] at hm
    have hbound := sym_den_le liveScale
      (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
      ⟨_, m.factors.map C10NaturalModeAtoms.nativeSymmetricAtom⟩
      (nativeWireCap sources k n) hfourS
      (by
        intro circuit hc
        obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hc
        rw [nativeSymmetric_wire atom (hm atom ha)]
        exact (hw atom ha).trans (le_max_right _ _))
    exact hbound.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (le_max_left _ _) _))

end capped

section loop
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {b : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}

/-- **D7 (`hden`)** at `denBits := nativeDenBits sources k p n`. -/
theorem loop_hden (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch
      (PolynomialClock.ordinaryClock k) n x oracle bits site mode ph b code)
    (hm : mode = CloseoutWitness.BoundedFields.symmetric bits) (liveScale : Nat) :
    ∀ m ∈ loopOrder L, (LiveRows.fraction sources liveScale
      (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
      mode m.factors).2 ≤ 2 ^ nativeDenBits sources k p n := by
  intro m hm'
  rw [hm]
  obtain ⟨l, hl, hml⟩ := List.mem_flatten.mp hm'
  obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
  exact fraction_den_le sources k p den x oracle bits liveScale ph c m (((L.trace c)._horder).subset hml)

end loop

/-- **D7 (`hdenwidth`)** at the schedule width, past the `Selection` onset. -/
theorem phase_hdenwidth (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k : Nat)
    (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : Nat} (hn : S.onset ≤ n) :
    nativeDenBits sources k p n + 1 ≤ C10PartsSchedule.entryWidthSchedule sources k S.exponent n :=
  (S.caps hn).1

/-- The threshold floor of the schedule width is at least one bit (a `Nat.size` of a positive denominator). -/
theorem thresholdFloor_pos (sources : EightSources) : 1 ≤ C10PartsSchedule.thresholdFloor sources := by
  unfold C10PartsSchedule.thresholdFloor C10ThresholdWidths.thresholdWidth
  exact le_trans (Nat.size_pos.mpr (Rat.den_pos _)) (le_trans (le_max_right _ _) (le_max_left _ _))

/-- **D7 with one bit of slack**: `nativeDenBits + 2 ≤ b` at the schedule width, since the width is the threshold
floor (at least one bit) PLUS the power that already exceeds `nativeDenBits` (`Selection.cap_le`). -/
theorem phase_hdenwidth2 (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k : Nat)
    (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : Nat} (hn : S.onset ≤ n) :
    nativeDenBits sources k p n + 2 ≤ C10PartsSchedule.entryWidthSchedule sources k S.exponent n := by
  have h := S.cap_le n hn
  unfold CloseoutFinalC10ModeNativeSchedule.jointCap at h
  have h1 : nativeDenBits sources k p n + 1 ≤ C10PartsSchedule.widthPower sources k S.exponent n :=
    (le_max_left _ _).trans h
  have h2 := thresholdFloor_pos sources
  unfold C10PartsSchedule.entryWidthSchedule
  omega

/-- The engine's strict form from `d ≤ 2^D` and `D + 2 ≤ b`. -/
theorem two_den_lt {d D b : Nat} (hd : d ≤ 2 ^ D) (hb : D + 2 ≤ b) : 2 * d < 2 ^ b := by
  have h1 : 2 * d ≤ 2 ^ (D+1) := by rw [pow_succ]; omega
  have h2 : 2 ^ (D+1) < 2 ^ (D+2) := Nat.pow_lt_pow_right (by decide) (by omega)
  have h3 : 2 ^ (D+2) ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
  omega

section strict

end strict

end
end NearCubicWires.SourcePhase
end
