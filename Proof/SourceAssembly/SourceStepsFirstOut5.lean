import Proof.SourceAssembly.SourceStepsStart5
import Proof.SourceAssembly.SourceFirstSeam5L

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

/-- **`first_seam5L`, with its conclusion named** (decision 99b). -/
theorem firstOut5_exists {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {si : Nat} (initM : Machine V si) {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc Rk b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps)
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family
        (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
        row)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordinate ph ci L target mode m) (layoutAt m) (factsAt m) (capsAt m))
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hG7 : ResidentRunH g7M g7cost mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext2.ext1.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (hminj : Function.Injective ((𝔇).maskSlots hV)) (hsinj : Function.Injective ((𝔇).pslots hV))
    (hfinj : Function.Injective ((𝔇).familySlots hV)) (hpinj : Function.Injective ((𝔇).poolSlots hV))
    (hrinj : Function.Injective (Dims.rewind2Slots e.ext2.ext1.ext hV))
    (hraw : (𝔇).pslots hV (packets (decompositionOf sources)).ordinary.program.outputTape = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 262).castAdd 1))
    (hpool : (𝔇).poolSlots hV 34 = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 0).castAdd 1))
    (hsrc : Dims.rewind2Slots e.ext2.ext1.ext hV 0 = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.descriptor (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork)).castAdd 1))
    (cnt c15 q284 c17 c18 : Fin V) (hcnt : cnt.val = (𝔇).U)
    (hlow : c15.val < (𝔇).F ∧ q284.val < (𝔇).F ∧ c17.val < (𝔇).F ∧ c18.val < (𝔇).F)
    (h1 : c15 ≠ q284) (h2 : c15 ≠ c17) (h3 : c15 ≠ c18) (h4 : q284 ≠ c17) (h5 : q284 ≠ c18) (h6 : c17 ≠ c18)
    (C : Nat) (wq : List Bool) (hwq : wq.length = C)
    (icost : Nat) (H0 Hi : Fin V → Nat) (A0 Ai : Fin V → List Bool) (hinit : Step initM icost H0 A0 Hi Ai)
    (Kc : Fin V → Prop) (w Mb Ms cW cQ cB cS S Rw B v U0 fuel0 : Nat)
    (hC : InvC e hV Rc Rk Kc K0 KH0 cnt w q Mb Ms cW cQ cB cS S Rw B v U0 Hi Ai)
    (hRk : Rc ≤ Rk) (hRc4 : 4 ≤ Rc)
    (hSl : S + 2 ≤ Rc) (hRl : Rw + 2 ≤ Rc) (hBl : B + 2 ≤ Rc) (hvl : v + 2 ≤ Rc) (hUl : U0 ≤ Rc)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc)
    (hKpos : ∀ x, K x → x.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e hV 10 ∧ x ≠ Dims.hrT e hV 11))
    (hKsub : ∀ x, K x → x ≠ c15 → x ≠ q284 → Kc x) (hKcnt : ∀ x, K x → x ≠ cnt)
    (hKfree : ∀ x, K x → Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).poolSlots hV)
      ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x ∨
      x = Dims.rewind2Slots e.ext2.ext1.ext hV 1 ∨ x = Dims.rewind2Slots e.ext2.ext1.ext hV 2)
    (hKr1 : K (Dims.rewind2Slots e.ext2.ext1.ext hV 1) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = List.replicate (capsAt 0).descriptorReserve true ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = 0)
    (hKr2 : K (Dims.rewind2Slots e.ext2.ext1.ext hV 2) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = List.replicate (capsAt 0).descriptorReserve false ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = 0)
    (hK15 : K c15 → K0 c15 = List.replicate C false ∧ KH0 c15 = 0)
    (hK284 : K q284 → K0 q284 = wq ∧ KH0 q284 = 0)
    (hq : Ai c15 = wq) (hq17 : Ai c17 = List.replicate C true) (hq18 : Ai c18 = List.replicate (C+1) false)
    (h284 : (Ai q284).length ≤ C)
    (hH15 : Hi c15 = 0) (hH284 : Hi q284 = 0) (hH17 : Hi c17 = 0) (hH18 : Hi c18 = 0)
    (hlong : ∀ x : Fin V, (𝔇).F ≤ x.val → x.val < (𝔇).U → Rc ≤ (Ai x).length)
    (hN : (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length).length ≤ Rc)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode 0).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode 0))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode 0))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode 0) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode 0))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^(q+1) < 2^w)
    (hdescR : (capsAt 0).descriptorReserve ≤ Rc) (hL : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length + 3 ≤ Rc)
    (hfamH0 : ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i + fuel0 + 1 ≤ Rc)
    (hwinI0 : g7cost 0 + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) + 1 ≤ Rc)
    (hwinZ0 : (g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) + 1 ≤ Rk)
    (firstCost : Nat)
    (hcost0 : (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (icost + 1 + ((4*Rk+7) + 1 + (((4*Rc+7) + 1 + ((4*Rc+7) + 1 + ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)))) + 1 + ((g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1 + (refreshCost Rc + 1 + ((2*Rc+4) + 1 + 1))))))) ≤ firstCost) :
    ∃ (H' : Fin V → Nat) (A' : Fin V → List Bool),
      firstOutP5 mask packets rows sources res p k r se sp e hV initM g7M coordinate ph ci L target mode Rc Rk b layoutAt factsAt K K0 KH0 hminj hsinj hfinj hpinj hrinj hraw hpool hsrc cnt c15 q284 c17 c18 H0 Hi A0 Ai w Mb Ms cW cQ cB cS S Rw B v U0 fuel0 firstCost H' A' :=
  first_seam5L mask packets rows sources res p k r se sp e hV initM g7M g7cost coordinate ph ci L target mode Rc Rk b layoutAt capsAt factsAt goodAt K K0 KH0 hG7 hminj hsinj hfinj hpinj hrinj hraw hpool hsrc cnt c15 q284 c17 c18 hcnt hlow h1 h2 h3 h4 h5 h6 C wq hwq icost H0 Hi A0 Ai hinit Kc w Mb Ms cW cQ cB cS S Rw B v U0 fuel0 hC hRk hRc4 hSl hRl hBl hvl hUl hMb hMs hKpos hKsub hKcnt hKfree hKr1 hKr2 hK15 hK284 hq hq17 hq18 h284 hH15 hH284 hH17 hH18 hlong hN hlog he1 hpw hfirst hsecond hdescR hL hfamH0 hwinI0 hwinZ0 firstCost hcost0

end concrete

end
end NearCubicWires.SourceSteps
end

