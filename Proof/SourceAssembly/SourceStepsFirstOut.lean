import Proof.SourceAssembly.SourceFirstSeam4L

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
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

/-- **`first_seam4L`'s conclusion at an exit `(H', A')`** (verbatim): the first cycle's `Prepared` run, the slot inputs of call `0`, the loop
counter, `InvR` at `0`, the `encT` heads/words, the frame below `F` and the lengths. -/
def firstOutP {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {si : Nat} (initM : Machine V si) {s7 : Nat} (g7M : Machine V s7)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc Rk b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family
        (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
        row)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hminj : Function.Injective ((𝔇).maskSlots hV)) (hsinj : Function.Injective ((𝔇).pslots hV))
    (hfinj : Function.Injective ((𝔇).familySlots hV)) (hpinj : Function.Injective ((𝔇).poolSlots hV))
    (hrinj : Function.Injective (Dims.rewind2Slots e.ext2.ext1.ext hV))
    (hraw : (𝔇).pslots hV (packets (decompositionOf sources)).ordinary.program.outputTape = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 262).castAdd 1))
    (hpool : (𝔇).poolSlots hV 34 = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 0).castAdd 1))
    (hsrc : Dims.rewind2Slots e.ext2.ext1.ext hV 0 = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.descriptor (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork)).castAdd 1))
    (cnt c15 q284 c17 c18 : Fin V)
    (H0 Hi : Fin V → Nat) (A0 Ai : Fin V → List Bool)
    (w Mb Ms cW cQ cB cS S Rw B v U0 fuel0 : Nat) (firstCost : Nat)
    (H' : Fin V → Nat) (A' : Fin V → List Bool) : Prop :=
      (Cycle.cycleCode mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) ((𝔇).maskSlots hV) hminj ((𝔇).pslots hV) hsinj ((𝔇).slot hV) ((𝔇).ret hV)
          ((𝔇).scr hV 0) ((𝔇).scr hV 1) ((𝔇).scr hV 2) ((𝔇).scr hV 3) ((𝔇).scr hV 4) ((𝔇).familySlots hV) hfinj
          ((𝔇).poolSlots hV) hpinj (Dims.rewind2Slots e.ext2.ext1.ext hV) hrinj hraw hpool hsrc
          ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
          (firstPro3 se sp e hV initM g7M cnt c15 q284 c17 c18) (Dims.csSlots e.ext2.ext1.ext hV) (Dims.natSlots hV) (Dims.drvSlots e.ext2.ext1.ext hV)).Prepared (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) firstCost H0 H' A0 A' ∧
      (∀ i, H' (Dims.natSlots hV i) = r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i) ∧
      (∀ i, A' (Dims.natSlots hV i) = ZeroPadding.pad Rc (r_inputT (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B
        (RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length) v (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i)) ∧
      (A' cnt = ZeroPadding.pad Rc (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length) ∧
        H' cnt = 1) ∧
      InvR e hV Rc Rk K K0 KH0 0 w q Mb Ms cW cQ cB cS S Rw B v U0 fuel0 H' A' ∧
      (∀ kk : Fin 13, H' (Dims.encT (d := 𝔇) hV kk) = Hi (Dims.encT (d := 𝔇) hV kk)) ∧
      A' (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^q))) ∧
      (∀ hm : 0 < (monomials coordinate ph ci).length, ∀ i : Fin 3,
        A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[0]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      (∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) → A' (Dims.encT (d := 𝔇) hV kk) = Ai (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ x : Fin V, x.val < (𝔇).F → Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV)
          ((𝔇).poolSlots hV) ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x → x ≠ c15 → x ≠ q284 →
        H' x = Hi x ∧ A' x = Ai x) ∧
      (∀ x : Fin V, (𝔇).F ≤ x.val → x.val < (𝔇).U → Rc ≤ (A' x).length)

end concrete

end
end NearCubicWires.SourceSteps
end

