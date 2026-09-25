import Proof.SourceAssembly.SourcePhaseAssembly

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
open NearCubicWires.SourceParent NearCubicWires.AggregateClauseExpansion
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## 1. List plumbing -/

theorem flatten_ofFn_perm {α : Type} : ∀ {m : Nat} (f g : Fin m → List α), (∀ i, (f i).Perm (g i)) →
    (List.ofFn f).flatten.Perm (List.ofFn g).flatten
  | 0, _, _, _ => by simp
  | m+1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons]
    exact (h 0).append (flatten_ofFn_perm _ _ (fun i => h i.succ))

theorem flatten_ofFn_forall₂ {α β : Type} {R : α → β → Prop} : ∀ {m : Nat} (f : Fin m → List α) (g : Fin m → List β),
    (∀ i, List.Forall₂ R (f i) (g i)) → List.Forall₂ R (List.ofFn f).flatten (List.ofFn g).flatten
  | 0, _, _, _ => by simp
  | m+1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons]
    exact List.rel_append (h 0) (flatten_ofFn_forall₂ _ _ (fun i => h i.succ))

theorem forall₂_of_index {α β : Type} (R : α → β → Prop) (l₁ : List α) (l₂ : List β)
    (hlen : l₂.length = l₁.length)
    (h : ∀ j (h1 : j < l₁.length) (h2 : j < l₂.length), R l₁[j] l₂[j]) : List.Forall₂ R l₁ l₂ :=
  List.forall₂_iff_get.mpr ⟨hlen.symm, fun i h1 h2 => h i h1 h2⟩

/-! ## 2. D1: the phase polynomial is the clause-ordered concatenation of the clauses' calls -/

theorem phase_monomials_perm {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (ph : Phase) (pcpp : SourceInterfaces.PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) :
    (CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials.Perm
      (List.ofFn fun ci => (CloseoutFinalC10SupplierCalls.siteCalls ph pcpp coordinate systematicAtom ci).monomials).flatten := by
  have hperm : (Finset.univ : Finset (Fin (2^pcpp.clauseBits))).toList.Perm (List.finRange (2^pcpp.clauseBits)) :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange _)).mpr (by simp)
  simp only [CloseoutFinalC10Exactness.phasePolynomial, CloseoutFinalC10SupplierCalls.siteCalls,
    CircuitPolynomial.scale, polynomialFinsetSum, polynomialSumList]
  have h2 := ((hperm.map (CloseoutFinalC10Exactness.sitePolynomial ph pcpp coordinate systematicAtom)).flatMap_right
    (fun p => p.monomials)).map (CircuitMonomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ)))
  refine h2.trans (List.Perm.of_eq ?_)
  simp only [List.ofFn_eq_map, List.map_flatMap, List.flatMap_map]
  rfl

section loop
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

/-- **D1 (`order`).** The phase order: the clause-ordered concatenation of the clauses' orders. -/
abbrev loopOrder (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph b code) : List (CircuitMonomial (C10TotalDecode.Atom (pcppAt sources k clock x oracle)) 4) :=
  (List.ofFn (fun c => (L.values c).order)).flatten

/-- **D1 (`horder`).** -/
theorem loop_horder (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph b code) :
    (Poly sources p k den clock n x oracle bits ph).monomials.Perm (loopOrder L) :=
  (phase_monomials_perm ph (pcppAt sources k clock x oracle)
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) C10TotalDecode.Atom.systematic).trans
    (flatten_ofFn_perm _ _ (fun c => ((L.trace c)._horder).symm))

/-- **D3 (`hrecords`).** The phase records, from the per-clause trace and appended entries, when every
clause uses the phase's `liveScale` and `target`. -/
theorem loop_hrecords (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph b code) (liveScale target : Nat)
    (hL : ∀ c, (L.values c).L = liveScale) (hT : ∀ c, (L.values c).target = target) :
    List.Forall₂ (fun m e =>
      e.coefficient = CloseoutFinalC10SupplierCalls.coefficientEstimate m.coefficient ∧
      e.count = (LiveRows.fraction sources liveScale target mode m.factors).1 ∧
      e.denominator = (LiveRows.fraction sources liveScale target mode m.factors).2) (loopOrder L) L.entries := by
  apply flatten_ofFn_forall₂
  intro c
  have tr := L.trace c
  have ap := L.appends c
  apply forall₂_of_index _ _ _ tr._hlen
  intro j h1 h2
  have hcoe := tr._hcoeff j h2
  obtain ⟨_layout, _hds, _hres, _hw, htot, hden⟩ := tr._hnative j h2
  rw [ap._hentries j h2]
  have gc : ((L.values c).order.map (fun m => m.coefficient)).getD j 0 = ((L.values c).order[j]).coefficient := by
    rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getElem_map]
  have gf : ((L.values c).order.map (fun m => m.factors)).getD j [] = ((L.values c).order[j]).factors := by
    rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getElem_map]
  rw [gc] at hcoe
  rw [gf, hL c, hT c] at htot hden
  exact ⟨hcoe, htot, hden⟩

end loop

end
end NearCubicWires.SourcePhase
end
