import Proof.SourceAssembly.SourceClauseChain5
import Proof.SourceAssembly.SourceRefillSeam5

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

/-- **`seam4U_spec` with the chain's end words**: the invariant also carries, at the last call `j = N ≥ 1`, the last call's emitter/appender
words on `encT 3, 5..12` (padded), from `refill_seam4`'s `A' (encT kk) = pad reserve (install app (install enc Aj E) T (encT kk))`. -/
theorem seam5W_spec (ph : Phase) {vE vP : PCJd4d1d9d7d1fa4313_Production.Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    {s7 : Nat} (g7M : Machine (UOf mask packets rows sources res p k r) s7) (g7cost : Nat → Nat)
    (preF : Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat) (mode : Bool) (Rc Rk b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps)
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family
        (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
        row)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordinate ph ci L target mode m) (layoutAt m) (factsAt m) (capsAt m))    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (hG7 : ResidentRunH g7M g7cost mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).slot 𝒽) ((𝔇).ret 𝒽) ((𝔇).scr 𝒽 0) ((𝔇).scr 𝒽 1)
      ((𝔇).familySlots 𝒽) ((𝔇).poolSlots 𝒽) (Dims.rewind2Slots e.ext2.ext1.ext 𝒽)
      ((𝔇).scr 𝒽 5) ((𝔇).scr 𝒽 6) ((𝔇).scr 𝒽 7) ((𝔇).scr 𝒽 8) ((𝔇).scr 𝒽 9) ((𝔇).scr 𝒽 10)
      (Dims.lenTape e.ext2.ext1.ext 𝒽) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e.ext2.ext1 𝒽 ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 𝒽 ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := UOf mask packets rows sources res p k r) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e.ext2.ext1 𝒽 ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    {Atom : Type} (vd : RCFive.Source.CallValues Atom (𝒞).sourceTapes)
    (w cW cQ Mb Ms cB cS S Rw B U0 refillCost N : Nat)
    -- the code's `enc`/`app` placement
    (hencP : ∀ i, (𝔇).F ≤ ((𝒞).enc i).val ∧ ((𝒞).enc i).val < (𝔇).G)
    (happP : ∀ i, ((𝒞).app i).val < (𝔇).F ∨ ((𝔇).F ≤ ((𝒞).app i).val ∧ ((𝒞).app i).val < (𝔇).G))
    -- the chain's per-call data in the seam's forms
    (hds : ∀ j, vd.ds (j+1) = dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1)))
    (hxs : ∀ j, (vd.xs (j+1)).length = (vd.ds (j+1)).length)
    (hS : ∀ j, vd.S j = S) (hR : ∀ j, vd.R j = Rw) (hB : ∀ j, vd.B j = B)
    (hrw : ∀ j, vd.rowWidth (j+1) = RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length)
    (hRes : vd.reserveSize = Rc) (hrc : vd.refillCost = refillCost)
    -- constants
    (hRk : Rc ≤ Rk) (hcW : Rc ≤ cW) (hcQ : Rc ≤ cQ) (hcB : Rc ≤ cB) (hcS : Rc ≤ cS)
    (hSl : S + 2 ≤ Rc) (hRl : Rw + 2 ≤ Rc) (hBl : B + 2 ≤ Rc) (hvl : b + 2 ≤ Rc) (hw2 : 2 * w + 1 ≤ Rc) (hUl : U0 ≤ Rc)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc)
    (hKpos : ∀ x, K x → x.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e 𝒽 10 ∧ x ≠ Dims.hrT e 𝒽 11))
    (hKpad : ∀ x, K x → (𝔇).F ≤ x.val → ZeroPadding.pad Rc (K0 x) = K0 x)
    (hKapp : ∀ x, K x → ∀ i, (𝒞).app i ≠ x)
    (hKfree : ∀ x, K x → Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽)
      ((𝔇).familySlots 𝒽) (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) x ∨
      x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1 ∨ x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2)
    (hKr1 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = List.replicate (capsAt (j+1)).descriptorReserve true ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = 0)
    (hKr2 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = List.replicate (capsAt (j+1)).descriptorReserve false ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = 0)
    -- per call `j < N`
    (hj : ∀ j, j < N → j + 1 ≤ (monomials coordinate ph ci).length)
    (hRc : ∀ j, j < N → j + 1 + 3 ≤ Rc)
    (henc0 : ∀ j, j < N → ∀ (A0 : Fin (UOf mask packets rows sources res p k r) → List Bool) (kk : Fin 13),
      (kk.val < 3 ∨ kk.val = 4) →
      (install (𝒞).app (install (𝒞).enc A0
        (e_bank b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j)
          (ZeroPadding.pad (vd.D j) (Stream.entryWord b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩))))
        (CloseoutFinalC10AppendPositioning.tapes b (vd.D j) (vd.logSize j) (vd.resetSize j)
          ⟨vd.coefficient j, vd.total j, vd.denominator j⟩
          ((vd.phasePrefix ++ vd.entries.take j) ++ [⟨vd.coefficient j, vd.total j, vd.denominator j⟩]))
        (Dims.encT (d := 𝔇) 𝒽 kk)).length ≤ Rc)
    (hlog : ∀ j, j < N → 2 * ((requestAt coordinate ph ci L target mode (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : ∀ j, j < N → 1 ≤ vE (requestAt coordinate ph ci L target mode (j+1)))
    (hpw : ∀ j, j < N → (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode (j+1)))).length ≤ w)
    (hfirst : ∀ j, j < N → vP (requestAt coordinate ph ci L target mode (j+1)) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode (j+1)))) < 2^w)
    (hsecond : ∀ j, j < N → vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^(q+1) < 2^w)
    (hdescR : ∀ j, j < N → (capsAt (j+1)).descriptorReserve ≤ Rc)
    (hL : ∀ j, j < N → (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length + 3 ≤ Rc)
    (hfamH : ∀ j, j < N → ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))).length i + (fuelOf 𝒞 b vd (j+1)) + 1 ≤ Rc)
    (hwinI : ∀ j, j < N → cursorCost j + 1 + g7cost (j+1) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B b (0)) + 1 ≤ Rc)
    (hwinZ : ∀ j, j < N → (restCost se sp g7cost (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms j) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B b (0)) + 1 ≤ Rk)
    (hcost : ∀ j, j < N → (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B b ((4*Rk+7) + 1 + ((4*Rc+7) + 1 + ((restCost se sp g7cost (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms j) + 1 + refreshCost Rc)))) ≤ refillCost)
    -- the clause bridge's data: the chain start, the code's `app` tapes
    (H0c : Fin (UOf mask packets rows sources res p k r) → Nat)
    (A0c : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (happInj : Function.Injective (𝒞).app) (hencInj : Function.Injective (𝒞).enc)
    (hcovE : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → ∃ i, (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 kk)
    (hcov : ∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) →
      (∃ i, (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 kk) ∨ (∃ i, (𝒞).app i = Dims.encT (d := 𝔇) 𝒽 kk))
    (happFree : ∀ i, ((𝒞).app i).val < (𝔇).F →
      Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽)
        (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) ((𝒞).app i))
    
    (hvCoef : ∀ j, j + 1 < N → ∀ hm : j + 1 < (monomials coordinate ph ci).length, ∀ (i : Fin 11) (kk : Fin 3),
      (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 ⟨kk.val, by omega⟩ →
      encInOf 𝒞 b vd (j+1) i = RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
        (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[j+1]).coefficient) 0 0 ⟨kk.val, by omega⟩))
    (hvDen : ∀ j, j + 1 < N → ∀ i : Fin 11, (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 4 →
      encInOf 𝒞 b vd (j+1) i = RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^q)))
    (hvEnc : ∀ j, j + 1 < N → ∀ i : Fin 11, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) → (∀ i', (𝒞).app i' ≠ (𝒞).enc i) →
      (∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (𝒞).enc i ≠ Dims.encT (d := 𝔇) 𝒽 kk) →
      encInOf 𝒞 b vd (j+1) i = encWOf b vd j i)
    (hvEA : ∀ j, j + 1 < N → ∀ (i : Fin 11) (i' : Fin 6), (𝒞).app i' = (𝒞).enc i → (∀ i'', (𝒞).slots i'' ≠ (𝒞).enc i) →
      encInOf 𝒞 b vd (j+1) i = appTOf b vd j i')
    (hvApp : ∀ j, j + 1 < N → ∀ i : Fin 6, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) →
      appInOf 𝒞 b vd (j+1) i = appTOf b vd j i) :
    SeamSpec N (fun _ => 0) (𝒞).slots (inTOf 𝒞 b vd)
      (fun j H A => Rest.InvR e 𝒽 Rc Rk K K0 KH0 j w q Mb Ms cW cQ cB cS S Rw B b U0 (fuelOf 𝒞 b vd j) H A ∧
        (∀ x : Fin (UOf mask packets rows sources res p k r), x.val < (𝔇).F →
          Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽)
            (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) x →
          (∀ i, (𝒞).app i ≠ x) → A x = A0c x ∧ H x = H0c x) ∧
        (∀ i, ((𝒞).app i).val < (𝔇).F → H ((𝒞).app i) = H0c ((𝒞).app i) ∧
          (0 < j → A ((𝒞).app i) = appTOf b vd (j-1) i)) ∧
        (∀ kk : Fin 13, H (Dims.encT (d := 𝔇) 𝒽 kk) = H0c (Dims.encT (d := 𝔇) 𝒽 kk)) ∧
        (j < N → (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) → A ((𝒞).enc i) = encInOf 𝒞 b vd j i) ∧
          (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) → A ((𝒞).app i) = appInOf 𝒞 b vd j i)) ∧
        (N ≤ j → 0 < j → ∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) →
          A (Dims.encT (d := 𝔇) 𝒽 kk) = ZeroPadding.pad Rc
            (install (𝒞).app (install (𝒞).enc (fun _ => []) (encWOf b vd (j-1))) (appTOf b vd (j-1)) (Dims.encT (d := 𝔇) 𝒽 kk))) ∧
        (N ≤ j → 0 < j → ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A (Dims.encT (d := 𝔇) 𝒽 kk)).length ≤ Rc))
      (goodOf 𝒞 b vd) := by
  intro j hjN H A hI5
  obtain ⟨hI, hKL, hAP, hEH, -, -, -⟩ := hI5
  have hB0 : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have hGF : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have hrt : (𝔇).rt = r_tapes (𝒞).a := rfl
  have slotv : ∀ i, ((𝒞).slots i).val = (𝔇).F + i.val := fun i => (𝒞)._hs i
  have venc : ∀ kk : Fin 13, (Dims.encT (d := 𝔇) 𝒽 kk).val = (𝔇).F + (𝔇).rt + kk.val := fun _ => rfl
  obtain ⟨H', Am, hprep, hnatH, hnatA, hInv', e1, e2a, e2b, e3a, e3b, e2L⟩ :=
    Rest.refill_seam5 mask packets rows sources res p k r se sp e 𝒽 g7M g7cost coordinate ph ci L target mode Rc Rk b
      layoutAt capsAt factsAt goodAt K K0 KH0 hG7
      ((𝔇).maskSlots_injective 𝒽) ((𝔇).pslots_injective 𝒽) ((𝔇).familySlots_injective 𝒽) ((𝔇).poolSlots_injective 𝒽)
      (rewind2_injective (dims_ext mask packets rows sources res p k r hres) 𝒽)
      (hrawR mask packets rows sources res p k r 𝒽) (hpoolR mask packets rows sources res p k r 𝒽)
      (hsrcR mask packets rows sources res hres p k r 𝒽)
      (𝒞).slots (fun _ => rfl) (𝒞).enc (𝒞).app hencP happP (reserveOf 𝒞 vd)
      (fun x => by unfold reserveOf; rw [hRes]; rfl)
      (famOf 𝒞) (fuelOf 𝒞 b vd j) H (outHOf 𝒞 vd j H) A
      (fun Z => r_outputT (𝒞).a (vd.ds j) (vd.S j) (vd.R j) (vd.B j) (vd.rowWidth j) b (vd.xs j) Z)
      (e_bank b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j)
        (ZeroPadding.pad (vd.D j) (Stream.entryWord b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩)))
      (CloseoutFinalC10AppendPositioning.tapes b (vd.D j) (vd.logSize j) (vd.resetSize j)
        ⟨vd.coefficient j, vd.total j, vd.denominator j⟩
        ((vd.phasePrefix ++ vd.entries.take j) ++
          [(⟨vd.coefficient j, vd.total j, vd.denominator j⟩ : Stream.Entry)]))
      (fun x hx => dockH_other _ _ _ x hx) j (hj j hjN) (hRc j hjN) hRk w cW cQ Mb Ms cB cS S Rw B b U0
      (fuelOf 𝒞 b vd (j+1)) hI hcW hcQ hcB hcS hSl hRl hBl hvl hUl hMb hMs hKpos hKpad hKapp hKfree
      (hKr1 j hjN) (hKr2 j hjN)
      (henc0 j hjN A) (hlog j hjN) (he1 j hjN) (hpw j hjN) (hfirst j hjN) (hsecond j hjN) (hdescR j hjN) (hL j hjN)
      (hfamH j hjN) (hwinI j hjN) (hwinZ j hjN) refillCost (hcost j hjN)
  -- the next family input on the slots
  have hAs : ∀ i, Am ((𝒞).slots i) = ZeroPadding.pad Rc (inTOf 𝒞 b vd (j+1) i) := by
    intro i
    show Am ((𝒞).slots i) = ZeroPadding.pad Rc (r_inputT (𝒞).a (vd.ds (j+1)) (vd.S (j+1)) (vd.R (j+1)) (vd.B (j+1))
      (vd.rowWidth (j+1)) b (vd.xs (j+1)).length i)
    rw [hxs j, hds j, hS, hR, hB, hrw j]
    exact hnatA i
  -- the reserve: `Rc` from `F` on, `0` below
  have hresF : ∀ y : Fin (UOf mask packets rows sources res p k r), (𝔇).F ≤ y.val → reserveOf 𝒞 vd y = Rc := by
    intro y hy
    unfold reserveOf
    rw [if_pos (by show PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ y.val; exact hy), hRes]
  have hresL : ∀ y : Fin (UOf mask packets rows sources res p k r), y.val < (𝔇).F → reserveOf 𝒞 vd y = 0 := by
    intro y hy
    unfold reserveOf
    rw [if_neg (by show ¬ (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ y.val); exact Nat.not_le.mpr hy)]
  have hsl : ∀ i, reserveOf 𝒞 vd ((𝒞).slots i) = Rc := fun i => hresF _ (by rw [slotv i]; omega)
  -- tapes below `F` are neither slots nor `enc` tapes
  have lowNS : ∀ x : Fin (UOf mask packets rows sources res p k r), x.val < (𝔇).F → ∀ i, (𝒞).slots i ≠ x := by
    intro x hx i h
    have h2 := congrArg Fin.val h
    rw [slotv i] at h2
    omega
  have lowE : ∀ x : Fin (UOf mask packets rows sources res p k r), x.val < (𝔇).F → ∀ i, (𝒞).enc i ≠ x := by
    intro x hx i h
    have h1 := (hencP i).1
    have h2 := congrArg Fin.val h
    omega
  have lowH : ∀ x : Fin (UOf mask packets rows sources res p k r), x.val < (𝔇).F → outHOf 𝒞 vd j H x = H x :=
    fun x hx => dockH_other _ _ _ x (lowNS x hx)
  have encNS : ∀ kk : Fin 13, ∀ i, (𝒞).slots i ≠ Dims.encT (d := 𝔇) 𝒽 kk := by
    intro kk i h
    have h2 := congrArg Fin.val h
    rw [slotv i, venc kk] at h2
    have := i.isLt
    omega
  -- a tape in `[F, F + rt)` is a slot, a tape in `[F + rt, G)` an `encT` tape
  have isSlot : ∀ x : Fin (UOf mask packets rows sources res p k r), (𝔇).F ≤ x.val → x.val < (𝔇).F + (𝔇).rt →
      ∃ i, (𝒞).slots i = x := fun x h1 h2 =>
    ⟨⟨x.val - (𝔇).F, by omega⟩, Fin.ext (by rw [slotv]; simp only; omega)⟩
  have isEncT : ∀ x : Fin (UOf mask packets rows sources res p k r), (𝔇).F + (𝔇).rt ≤ x.val → x.val < (𝔇).G →
      ∃ kk : Fin 13, Dims.encT (d := 𝔇) 𝒽 kk = x := fun x h1 h2 =>
    ⟨⟨x.val - ((𝔇).F + (𝔇).rt), by omega⟩, Fin.ext (by rw [venc]; simp only; omega)⟩
  have offSlotT : ∀ x : Fin (UOf mask packets rows sources res p k r), (∀ i, (𝒞).slots i ≠ x) → (𝔇).F ≤ x.val →
      x.val < (𝔇).G → ∃ kk : Fin 13, Dims.encT (d := 𝔇) 𝒽 kk = x := by
    intro x hs h1 h2
    by_cases h : x.val < (𝔇).F + (𝔇).rt
    · obtain ⟨i, hi⟩ := isSlot x h1 h
      exact absurd hi (hs i)
    · exact isEncT x (by omega) h2
  -- the machine bank on every `enc` tape off the slots: the next call's exact emitter words, padded
  have hmE : j + 1 < N → ∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) →
      ZeroPadding.pad Rc (encInOf 𝒞 b vd (j+1) i) = Am ((𝒞).enc i) := by
    intro hlt i hs
    obtain ⟨kk, hkk⟩ := offSlotT _ hs (hencP i).1 (hencP i).2
    have hm : j + 1 < (monomials coordinate ph ci).length := by have := hj (j+1) hlt; omega
    rcases (by omega : kk.val < 3 ∨ kk.val = 4 ∨ (kk.val = 3 ∨ 5 ≤ kk.val)) with h | h | h
    · have hk : (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 ⟨(⟨kk.val, h⟩ : Fin 3).val, by omega⟩ := hkk.symm
      rw [hvCoef j hlt hm i ⟨kk.val, h⟩ hk, hk]
      exact (e2b hm ⟨kk.val, h⟩).symm
    · have hk : (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 4 := hkk.symm.trans (congrArg _ (Fin.ext h))
      rw [hvDen j hlt i hk, hk]
      exact e2a.symm
    · have h3 := e3a kk h
      rw [hkk, hresF _ (hencP i).1] at h3
      rw [h3]
      refine congrArg (ZeroPadding.pad Rc) ?_
      by_cases ha : ∃ i', (𝒞).app i' = (𝒞).enc i
      · obtain ⟨i', hi'⟩ := ha
        rw [← hi']
        exact (hvEA j hlt i i' hi' hs).trans (install_slot _ happInj _ _ i').symm
      · have ha' : ∀ i', (𝒞).app i' ≠ (𝒞).enc i := fun i' hh => ha ⟨i', hh⟩
        have hne : ∀ kk' : Fin 13, (kk'.val < 3 ∨ kk'.val = 4) → (𝒞).enc i ≠ Dims.encT (d := 𝔇) 𝒽 kk' := by
          intro kk' hk' hh
          have hv := congrArg Fin.val (hkk.trans hh)
          rw [venc, venc] at hv
          omega
        exact (hvEnc j hlt i hs ha' hne).trans
          ((install_slot _ hencInj _ _ i).symm.trans (install_other _ _ _ _ ha').symm)
  -- the machine bank on every `app` tape off the slots and off `enc`: the next call's exact appender words, padded
  have hmA : j + 1 < N → ∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) →
      ZeroPadding.pad (reserveOf 𝒞 vd ((𝒞).app i)) (appInOf 𝒞 b vd (j+1) i) = Am ((𝒞).app i) := by
    intro hlt i hs he
    rcases happP i with hlo | ⟨hge, hlt2⟩
    · obtain ⟨-, a2⟩ := e3b _ hlo (happFree i hlo)
      rw [hresL _ hlo, ZeroPadding.pad_zero, a2]
      exact (hvApp j hlt i hs he).trans (install_slot _ happInj _ _ i).symm
    · obtain ⟨kk, hkk⟩ := offSlotT _ hs hge hlt2
      have hk : kk.val = 3 ∨ 5 ≤ kk.val := by
        by_contra hc
        obtain ⟨i'', hi''⟩ := hcovE kk (by omega)
        exact he i'' (hi''.trans hkk)
      have h3 := e3a kk hk
      rw [hkk, hresF _ hge] at h3
      rw [h3, hresF _ hge]
      exact congrArg (ZeroPadding.pad Rc) ((hvApp j hlt i hs he).trans (install_slot _ happInj _ _ i).symm)
  -- the next bank re-installs its slots; below `F` off `app` it is the machine bank
  have hfix : install (𝒞).slots (chainView 𝒞 b vd N (j+1) Am) (inTOf 𝒞 b vd (j+1)) = chainView 𝒞 b vd N (j+1) Am :=
    chainView_install_slots 𝒞 b vd N (j+1) Am
  have chainLow : ∀ x : Fin (UOf mask packets rows sources res p k r), x.val < (𝔇).F → (∀ i, (𝒞).app i ≠ x) →
      chainView 𝒞 b vd N (j+1) Am x = Am x := by
    intro x hx ha
    by_cases hlt : j + 1 < N
    · rw [chainView_lt 𝒞 b vd N (j+1) hlt]
      exact viewOf_other 𝒞 b vd (j+1) Am x (lowNS x hx) (lowE x hx) ha
    · rw [chainView_ge 𝒞 b vd N (j+1) (by omega)]
      exact install_other _ _ _ x (lowNS x hx)
  have hKposG : ∀ x, K x → x.val < (𝔇).F ∨ (𝔇).G ≤ x.val := by
    intro x hx
    rcases hKpos x hx with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  -- the next family input's words fit in `Rc` (the slots are dirt)
  have hSlen : ∀ i, (inTOf 𝒞 b vd (j+1) i).length ≤ Rc := by
    intro i
    have hd := hInv'.dirtA ((𝒞).slots i) (Or.inl (Or.inl (by rw [slotv i]; have := i.isLt; omega)))
      (by unfold SourceConstruction.Dims.InZ; rw [slotv i]; have := i.isLt; omega)
    have hd2 : (Am ((𝒞).slots i)).length ≤ Rc := hd
    rw [hAs i, ZeroPadding.pad_length] at hd2
    exact (le_max_right _ _).trans hd2
  refine ⟨H', chainView 𝒞 b vd N (j+1) Am, ⟨fun Z hstep => ?_, fun i => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `_hrefill`: the machine bank is the re-padded view
    have hp := hprep Z hstep
    have hlen : ∀ x, reserveOf 𝒞 vd x ≤ (Am x).length := by
      intro x
      refine le_trans ?_ (CloseoutFinalC10WorkerEmitShape.Step_length_le (Cycle.prepared_step _ _ _ _ _ _ _ hp) x)
      rw [ZeroPadding.pad_length]
      exact le_max_left _ _
    have hview : (fun x => ZeroPadding.pad (reserveOf 𝒞 vd x) (chainView 𝒞 b vd N (j+1) Am x)) = Am := by
      by_cases hlt : j + 1 < N
      · rw [chainView_lt 𝒞 b vd N (j+1) hlt]
        exact pad_viewOf 𝒞 b vd hencInj happInj (reserveOf 𝒞 vd) (j+1) Am (fun i => by rw [hsl i, hAs i])
          (fun i hs => by rw [hresF _ (hencP i).1]; exact hmE hlt i hs) (hmA hlt) (fun x _ _ _ => hlen x)
      · rw [chainView_ge 𝒞 b vd N (j+1) (by omega)]
        exact pad_install_slots 𝒞 b vd (reserveOf 𝒞 vd) (j+1) Am (fun i => by rw [hsl i, hAs i]) (fun x _ => hlen x)
    rw [hview, hds j, hrc]
    exact hp
  · show H' ((𝒞).slots i) = r_inputH (𝒞).a (vd.ds (j+1)) (vd.S (j+1)) (vd.R (j+1)) (vd.B (j+1)) (vd.xs (j+1)).length i
    rw [hxs j, hds j, hS, hR, hB]
    exact hnatH i
  · funext x
    rw [hfix]
    exact ZeroPadding.pad_zero _
  · -- (1) `InvR` at the view
    refine (congrArg (Rest.InvR e 𝒽 Rc Rk K K0 KH0 (j+1) w q Mb Ms cW cQ cB cS S Rw B b U0 (fuelOf 𝒞 b vd (j+1)) H') hfix).mpr ?_
    by_cases hlt : j + 1 < N
    · refine (congrArg (Rest.InvR e 𝒽 Rc Rk K K0 KH0 (j+1) w q Mb Ms cW cQ cB cS S Rw B b U0 (fuelOf 𝒞 b vd (j+1)) H')
        (chainView_lt 𝒞 b vd N (j+1) hlt Am)).mpr ?_
      exact invR_viewOf mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e g7M) preF
        hInv' hKposG hKapp hencP happP (j+1) hSlen
    · refine (congrArg (Rest.InvR e 𝒽 Rc Rk K K0 KH0 (j+1) w q Mb Ms cW cQ cB cS S Rw B b U0 (fuelOf 𝒞 b vd (j+1)) H')
        (chainView_ge 𝒞 b vd N (j+1) (by omega) Am)).mpr ?_
      exact Rest.InvR.view hInv' hKposG (𝒞).slots (fun _ => rfl) (slots_injective 𝒞) (inTOf 𝒞 b vd (j+1))
        (fun i => by rw [hAs i, ZeroPadding.pad_length]; exact le_max_right _ _)
  · -- (2) the chain start's words and heads below `F`, off the `app` tapes
    intro x hx hf happ
    rw [hfix]
    obtain ⟨a1, a2⟩ := e3b x hx hf
    rw [chainLow x hx happ, a2, install_other _ _ _ x happ, install_other _ _ _ x (lowE x hx), a1, lowH x hx]
    exact hKL x hx hf happ
  · -- (3) the `app` tapes below `F`: heads kept, words = the last call's append words
    intro i hi
    rw [hfix]
    obtain ⟨a1, a2⟩ := e3b _ hi (happFree i hi)
    refine ⟨by rw [a1, lowH _ hi]; exact (hAP i hi).1, fun _ => ?_⟩
    show chainView 𝒞 b vd N (j+1) Am ((𝒞).app i) = appTOf b vd j i
    by_cases hlt : j + 1 < N
    · rw [chainView_lt 𝒞 b vd N (j+1) hlt, viewOf_app 𝒞 b vd happInj (j+1) Am i (lowNS _ hi) (lowE _ hi)]
      exact hvApp j hlt i (lowNS _ hi) (lowE _ hi)
    · rw [chainView_ge 𝒞 b vd N (j+1) (by omega), install_other _ _ _ _ (lowNS _ hi), a2]
      exact install_slot _ happInj _ _ i
  · -- (4) every `encT` head is the chain start's
    intro kk
    exact (e1 kk).trans ((dockH_other _ _ _ _ (encNS kk)).trans (hEH kk))
  · -- (5) the exact `_hfields` words while a call follows
    intro hlt
    rw [hfix, chainView_lt 𝒞 b vd N (j+1) hlt]
    exact ⟨fun i hs => viewOf_enc 𝒞 b vd hencInj (j+1) Am i hs,
      fun i hs he => viewOf_app 𝒞 b vd happInj (j+1) Am i hs he⟩
  · -- (6) the last call's emitter/appender words on `encT` at the chain's end
    intro hNj _ kk hk
    rw [hfix, chainView_ge 𝒞 b vd N (j+1) hNj]
    refine (install_other _ _ _ _ (encNS kk)).trans ?_
    have h3 := e3a kk hk
    rw [hresF _ (by rw [venc]; omega)] at h3
    rw [h3, Nat.add_sub_cancel]
    exact congrArg (ZeroPadding.pad Rc) (install_cov (𝒞).enc (𝒞).app hencInj happInj A (fun _ => []) _ _ _ (hcov kk hk))
  · 
    intro hNj _ kk hk
    rw [hfix, chainView_ge 𝒞 b vd N (j+1) hNj]
    refine (congrArg List.length (install_other _ _ _ _ (encNS kk))).trans_le ?_
    rcases hk with hk | hk
    · exact e2L ⟨kk.val, hk⟩
    · have hk4 : kk = 4 := Fin.ext hk
      subst hk4
      rw [e2a]
      have hl : ∀ v, (RepairOrdinary.frame (SignedSortKey.binary w v)).length ≤ Rc := by
        intro v
        simp
        omega
      have hp : ∀ (l : List Bool), l.length ≤ Rc → (ZeroPadding.pad Rc l).length ≤ Rc := by
        intro l hl'
        simp only [ZeroPadding.pad, List.length_append, List.length_replicate]
        omega
      exact hp _ (hl _)

end seam

end
end NearCubicWires.SourceConstruction.Bridge
end
