import Proof.SourceAssembly.SourceSkelChainTrace
import Proof.SourceAssembly.SourceSkelSeam3
import Proof.SourceAssembly.SourceFirstSeam3L

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
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- **`_hfirst` from one `Prepared` at the loop's entry configuration** (verbatim field text at `values := vv`). -/
theorem hfirst_of_start (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (vv : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes)
    (Hs : Fin ((code ph).sourceTapes + 1) → Nat) (As : Fin ((code ph).sourceTapes + 1) → List Bool)
    (hP :
    let a := (code ph).a
    let sourceTapes := (code ph).sourceTapes
    let slots := (code ph).slots
    let enc := (code ph).enc
    let app := (code ph).app
    let refillCode := (code ph).refillCode
    let firstCode := (code ph).firstCode
    let whole := (code ph).whole
    let ds := vv.ds
    let entries := vv.entries
    let H := vv.H
    let A := vv.A
    let reserveSize := vv.reserveSize
    let firstCost := vv.firstCost
    let counterReserve := vv.counterReserve
    let refillCycle := refillCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let queried := install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) A0
       (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) ((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))) (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity ci.val
         (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity))
         (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).left,
           literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).right]))
    let originalH := fun i=>H0 (whole i)
    let originalA := fun i=>queried (whole i)
    let counterCaps : Fin (sourceTapes+1) → Nat := fun i=>if i.val=sourceTapes then counterReserve else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    let body := Composition.machine family refill
    let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration sourceTapes _)
    MaskFamilyCode.Prepared firstCode (ds 0) firstCost originalH Hs originalA As)
    (hHs : (Fin.addCases (vv.H 0) (fun _ : Fin 1 => (1 : Nat)) : Fin ((code ph).sourceTapes + 1) → Nat) = Hs)
    (hAs : (fun i : Fin ((code ph).sourceTapes + 1) => ZeroPadding.pad (if i.val = (code ph).sourceTapes then vv.counterReserve else 0)
      ((Fin.addCases (fun y : Fin (code ph).sourceTapes =>
          ZeroPadding.pad (if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ y.val then vv.reserveSize else 0) (vv.A 0 y))
        (fun _ : Fin 1 => CompareMachine.word vv.entries.length) : Fin ((code ph).sourceTapes + 1) → List Bool) i)) = As) :
    let a := (code ph).a
    let sourceTapes := (code ph).sourceTapes
    let slots := (code ph).slots
    let enc := (code ph).enc
    let app := (code ph).app
    let refillCode := (code ph).refillCode
    let firstCode := (code ph).firstCode
    let whole := (code ph).whole
    let ds := vv.ds
    let entries := vv.entries
    let H := vv.H
    let A := vv.A
    let reserveSize := vv.reserveSize
    let firstCost := vv.firstCost
    let counterReserve := vv.counterReserve
    let refillCycle := refillCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let queried := install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) A0
       (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) ((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))) (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity ci.val
         (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity))
         (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).left,
           literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).right]))
    let originalH := fun i=>H0 (whole i)
    let originalA := fun i=>queried (whole i)
    let counterCaps : Fin (sourceTapes+1) → Nat := fun i=>if i.val=sourceTapes then counterReserve else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    let body := Composition.machine family refill
    let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration sourceTapes _)
    MaskFamilyCode.Prepared firstCode (ds 0) firstCost originalH
       (RepeatMachine.cfg 0 (state 0 []) entries.length 1).heads originalA
       (fun i=>ZeroPadding.pad (counterCaps i) ((RepeatMachine.cfg 0 (state 0 []) entries.length 1).tapes i)) := by
  subst hHs
  subst hAs
  exact hP

/-- **The loop's padded entry tapes ARE the counter universe's exit** at the unpadded view (generic). -/
theorem loopStart_tapes {U t : Nat} (A' : Fin (U+1) → List Bool) (reserve : Fin U → Nat) (slots : Fin t → Fin U)
    (hinj : Function.Injective slots) (inT : Fin t → List Bool) (Rc cR N : Nat)
    (hsl : ∀ i, reserve (slots i) = Rc) (hfA : ∀ i, A' (slots i).castSucc = ZeroPadding.pad Rc (inT i))
    (hlong : ∀ y : Fin U, reserve y ≤ (A' y.castSucc).length)
    (hlast : A' (Fin.last U) = ZeroPadding.pad cR (CompareMachine.word N)) :
    (fun i : Fin (U+1) => ZeroPadding.pad (if i.val = U then cR else 0)
      ((Fin.addCases (fun y : Fin U => ZeroPadding.pad (reserve y) (install slots (fun z => A' z.castSucc) inT y))
        (fun _ : Fin 1 => CompareMachine.word N) : Fin (U+1) → List Bool) i)) = A' := by
  funext i
  refine Fin.addCases (fun y => ?_) (fun j => ?_) i
  · have hy : (Fin.castAdd 1 y).val ≠ U := by simp only [Fin.val_castAdd]; exact Nat.ne_of_lt y.isLt
    beta_reduce
    rw [if_neg hy, ZeroPadding.pad_zero, Fin.addCases_left]
    by_cases hx : ∃ i, slots i = y
    · obtain ⟨i, rfl⟩ := hx
      rw [install_slot slots hinj _ inT i, hsl i, ← hfA i]
      rfl
    · rw [install_other slots _ inT y (fun i h => hx ⟨i, h⟩)]
      exact Rest.pad_long _ _ (hlong y)
  · have hj : (Fin.natAdd U j).val = U := by simp only [Fin.val_natAdd]; have := j.isLt; omega
    have hl : Fin.natAdd U j = Fin.last U := Fin.ext (by rw [hj]; rfl)
    beta_reduce
    rw [if_pos hj, Fin.addCases_right, hl, hlast]

/-- **The loop's entry heads ARE the counter universe's exit heads** (generic). -/
theorem loopStart_heads {U : Nat} (H' : Fin (U+1) → Nat) (hlast : H' (Fin.last U) = 1) :
    (Fin.addCases (fun y : Fin U => H' y.castSucc) (fun _ : Fin 1 => (1 : Nat)) : Fin (U+1) → Nat) = H' := by
  funext i
  refine Fin.addCases (fun y => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]; rfl
  · have hl : Fin.natAdd U j = Fin.last U := Fin.ext (by simp only [Fin.val_natAdd, Fin.val_last]; have := j.isLt; omega)
    rw [Fin.addCases_right, hl, hlast]

section start
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽1" => UOf_le_succ mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph refill preF

/-- **The chain start from the first seam's exit** on the concrete code: the first family input on the slots (`hH0`, `hA0`), `InvR 0` at
the unpadded view on the source universe, and the two loop-entry equations `hfirst_of_start` consumes. -/
theorem first_start (ph : Phase) (refill : Σ s, Machine (UOf mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat) (mode : Bool) (Rc Rk b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family
        (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
        row)
    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (K1 : Fin (UOf mask packets rows sources res p k r + 1) → Prop)
    (K01 : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)
    (KH01 : Fin (UOf mask packets rows sources res p k r + 1) → Nat)
    (w Mb Ms cW cQ cB cS S Rw B U0 : Nat)
    {Atom : Type} (vd : RCFive.Source.CallValues Atom (𝒞).sourceTapes)
    -- the clause's data at call `0` (as `seam3_spec`'s at `j+1`)
    (hds0 : vd.ds 0 = dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0))
    (hxs0 : (vd.xs 0).length = (vd.ds 0).length)
    (hS0 : vd.S 0 = S) (hR0 : vd.R 0 = Rw) (hB0 : vd.B 0 = B)
    (hrw0 : vd.rowWidth 0 = RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length)
    (hRes : vd.reserveSize = Rc) (hcR : vd.counterReserve = Rc)
    (hNm : vd.entries.length = (monomials coordinate ph ci).length)
    -- the kept sets (`seam3_spec`'s `hKpos`; the first prologue's `K1` restricts to `K`)
    (hKpos : ∀ y, K y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc eX pX gW ≤ y.val ∧ y ≠ Dims.hrT e 𝒽 10 ∧ y ≠ Dims.hrT e 𝒽 11))
    (hK : ∀ y, K y → K1 y.castSucc) (hK0 : ∀ y, K y → K01 y.castSucc = K0 y ∧ KH01 y.castSucc = KH0 y)
    -- `first_seam3L`'s exit and the conclusions used
    (H' : Fin (UOf mask packets rows sources res p k r + 1) → Nat)
    (A' : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)
    (cnt : Fin (UOf mask packets rows sources res p k r + 1)) (hcnt : cnt.val = (𝔇).U)
    (hnatH : ∀ i, H' (Dims.natSlots 𝒽1 i) = r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i)
    (hnatA : ∀ i, A' (Dims.natSlots 𝒽1 i) = ZeroPadding.pad Rc (r_inputT (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B
      (RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length) b (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i))
    (hcA : A' cnt = ZeroPadding.pad Rc (CompareMachine.word (monomials coordinate ph ci).length)) (hcH : H' cnt = 1)
    (hInv : InvR e 𝒽1 Rc Rk K1 K01 KH01 0 w q Mb Ms cW cQ cB cS S Rw B b U0 (fuelOf 𝒞 b vd 0) H' A')
    (hlong : ∀ y : Fin (UOf mask packets rows sources res p k r + 1), (𝔇).F ≤ y.val → y.val < (𝔇).U → Rc ≤ (A' y).length) :
    (∀ i, (fun y => H' y.castSucc) ((𝒞).slots i) = r_inputH (𝒞).a (vd.ds 0) (vd.S 0) (vd.R 0) (vd.B 0) (vd.xs 0).length i) ∧
    (∀ i, install (𝒞).slots (fun y => A' y.castSucc) (inTOf 𝒞 b vd 0) ((𝒞).slots i) =
      r_inputT (𝒞).a (vd.ds 0) (vd.S 0) (vd.R 0) (vd.B 0) (vd.rowWidth 0) b (vd.xs 0).length i) ∧
    InvR e 𝒽 Rc Rk K K0 KH0 0 w q Mb Ms cW cQ cB cS S Rw B b U0 (fuelOf 𝒞 b vd 0) (fun y => H' y.castSucc)
      (install (𝒞).slots (fun y => A' y.castSucc) (inTOf 𝒞 b vd 0)) ∧
    (Fin.addCases (fun y : Fin (𝒞).sourceTapes => H' y.castSucc) (fun _ : Fin 1 => (1 : Nat)) : Fin ((𝒞).sourceTapes + 1) → Nat) = H' ∧
    (fun i : Fin ((𝒞).sourceTapes + 1) => ZeroPadding.pad (if i.val = (𝒞).sourceTapes then vd.counterReserve else 0)
      ((Fin.addCases (fun y : Fin (𝒞).sourceTapes =>
          ZeroPadding.pad (if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ y.val then vd.reserveSize else 0)
            (install (𝒞).slots (fun z => A' z.castSucc) (inTOf 𝒞 b vd 0) y))
        (fun _ : Fin 1 => CompareMachine.word vd.entries.length) : Fin ((𝒞).sourceTapes + 1) → List Bool) i)) = A' := by
  have hsl : ∀ i, ((𝒞).slots i).castSucc = Dims.natSlots 𝒽1 i := fun _ => Fin.ext rfl
  have hin : ∀ i, inTOf 𝒞 b vd 0 i = r_inputT (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length) b (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i := by
    intro i
    show r_inputT (printerOf sources) (vd.ds 0) (vd.S 0) (vd.R 0) (vd.B 0) (vd.rowWidth 0) b (vd.xs 0).length i = _
    rw [hxs0, hds0, hS0, hR0, hB0, hrw0]
  have hfA : ∀ i, A' ((𝒞).slots i).castSucc = ZeroPadding.pad Rc (inTOf 𝒞 b vd 0 i) := by
    intro i; rw [hsl i, hnatA i, hin i]
  have hlast : Fin.last (UOf mask packets rows sources res p k r) = cnt := Fin.ext (by rw [hcnt]; rfl)
  have hBG : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  refine ⟨fun i => ?_, fun i => install_slot _ (slots_injective 𝒞) _ _ i, ?_, ?_, ?_⟩
  · show H' ((𝒞).slots i).castSucc = _
    rw [hsl i, hnatH i, hxs0, hds0, hS0, hR0, hB0]
    rfl
  · refine InvR.view (InvR.restrict hInv K K0 KH0 hK hK0) (fun y hy => ?_) (𝒞).slots (fun _ => rfl) (slots_injective 𝒞)
      (inTOf 𝒞 b vd 0) (fun i => ?_)
    · rcases hKpos y hy with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · show (inTOf 𝒞 b vd 0 i).length ≤ (A' ((𝒞).slots i).castSucc).length
      rw [hfA i, ZeroPadding.pad_length]
      exact Nat.le_max_right _ _
  · exact loopStart_heads H' (by rw [hlast]; exact hcH)
  · refine loopStart_tapes A' _ (𝒞).slots (slots_injective 𝒞) (inTOf 𝒞 b vd 0) Rc vd.counterReserve vd.entries.length
      (fun i => ?_) hfA (fun y => ?_) (by rw [hlast, hcA, hcR, hNm])
    · show (if _ ≤ ((𝒞).slots i).val then vd.reserveSize else 0) = Rc
      rw [if_pos (by show _ ≤ _ + _ + i.val; omega), hRes]
    · show (if _ ≤ y.val then vd.reserveSize else 0) ≤ _
      split_ifs with hy
      · rw [hRes]; exact hlong y.castSucc hy y.isLt
      · exact Nat.zero_le _

end start

end
end NearCubicWires.SourceSkeleton
end
