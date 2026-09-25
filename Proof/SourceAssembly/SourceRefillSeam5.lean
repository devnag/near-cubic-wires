import Proof.SourceAssembly.SourceRefillSeam4
import Proof.SourceAssembly.SourceRefillPro5

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction
noncomputable section

namespace Rest

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

theorem refill_seam5 {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
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
    {t2 t3 : Nat} (slots : Fin (𝔇).rt → Fin V) (hslots : ∀ i, (slots i).val = (𝔇).F + i.val)
    (enc : Fin t2 → Fin V) (app : Fin t3 → Fin V)
    (hencP : ∀ i, (𝔇).F ≤ (enc i).val ∧ (enc i).val < (𝔇).G)
    (happP : ∀ i, (app i).val < (𝔇).F ∨ ((𝔇).F ≤ (app i).val ∧ (app i).val < (𝔇).G))
    (reserve : Fin V → Nat) (hreserve : ∀ x : Fin V, reserve x = if (𝔇).F ≤ x.val then Rc else 0)
    {ι : Type} {sf : Nat} (fm : Machine V sf) (n : Nat) (Hj Hout : Fin V → Nat) (Aj : Fin V → List Bool)
    (Y : ι → Fin (𝔇).rt → List Bool) (E : Fin t2 → List Bool) (T : Fin t3 → List Bool)
    (hHout : ∀ x, (∀ i, slots i ≠ x) → Hout x = Hj x)
    (j : Nat) (hj : j + 1 ≤ (monomials coordinate ph ci).length) (hRc : j + 1 + 3 ≤ Rc) (hRk : Rc ≤ Rk)
    (w cW cQ Mb Ms cB cS S Rw B v U0 fuel' : Nat)
    (hInv : InvR e hV Rc Rk K K0 KH0 j w q Mb Ms cW cQ cB cS S Rw B v U0 n Hj Aj)
    (hcW : Rc ≤ cW) (hcQ : Rc ≤ cQ) (hcB : Rc ≤ cB) (hcS : Rc ≤ cS)
    (hSl : S + 2 ≤ Rc) (hRl : Rw + 2 ≤ Rc) (hBl : B + 2 ≤ Rc) (hvl : v + 2 ≤ Rc) (hUl : U0 ≤ Rc)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc)
    (hKpos : ∀ x, K x → x.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e hV 10 ∧ x ≠ Dims.hrT e hV 11))
    (hKpad : ∀ x, K x → (𝔇).F ≤ x.val → ZeroPadding.pad Rc (K0 x) = K0 x)
    (hKapp : ∀ x, K x → ∀ i, app i ≠ x)
    (hKfree : ∀ x, K x → Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).poolSlots hV)
      ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x ∨
      x = Dims.rewind2Slots e.ext2.ext1.ext hV 1 ∨ x = Dims.rewind2Slots e.ext2.ext1.ext hV 2)
    (hKr1 : K (Dims.rewind2Slots e.ext2.ext1.ext hV 1) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = List.replicate (capsAt (j+1)).descriptorReserve true ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = 0)
    (hKr2 : K (Dims.rewind2Slots e.ext2.ext1.ext hV 2) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = List.replicate (capsAt (j+1)).descriptorReserve false ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = 0)
    (henc0 : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) →
      (install app (install enc Aj E) T (Dims.encT (d := 𝔇) hV kk)).length ≤ Rc)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode (j+1)))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode (j+1)))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode (j+1)) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode (j+1)))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^(q+1) < 2^w)
    (hdescR : (capsAt (j+1)).descriptorReserve ≤ Rc) (hL : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length + 3 ≤ Rc)
    (hfamH : ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))).length i + fuel' + 1 ≤ Rc)
    (hwinI : cursorCost j + 1 + g7cost (j+1) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) + 1 ≤ Rc)
    (hwinZ : (restCost se sp g7cost (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms j) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) + 1 ≤ Rk)
    (refillCost : Nat)
    (hcost : (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v ((4*Rk+7) + 1 + ((4*Rc+7) + 1 + ((restCost se sp g7cost (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms j) + 1 + refreshCost Rc)))) ≤ refillCost) :
    ∃ (H' : Fin V → Nat) (A' : Fin V → List Bool),
      (∀ z, Step fm n Hj Aj Hout (install app (install enc (install slots Aj (Y z)) E) T) →
        (Cycle.cycleCode mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) ((𝔇).maskSlots hV) hminj ((𝔇).pslots hV) hsinj ((𝔇).slot hV) ((𝔇).ret hV)
          ((𝔇).scr hV 0) ((𝔇).scr hV 1) ((𝔇).scr hV 2) ((𝔇).scr hV 3) ((𝔇).scr hV 4) ((𝔇).familySlots hV) hfinj
          ((𝔇).poolSlots hV) hpinj (Dims.rewind2Slots e.ext2.ext1.ext hV) hrinj hraw hpool hsrc
          ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
          (refillPro3 se sp e hV g7M) (Dims.csSlots e.ext2.ext1.ext hV) (Dims.natSlots hV) (Dims.drvSlots e.ext2.ext1.ext hV)).Prepared (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))) refillCost Hout H' (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) A') ∧
      (∀ i, H' (Dims.natSlots hV i) = r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))).length i) ∧
      (∀ i, A' (Dims.natSlots hV i) = ZeroPadding.pad Rc (r_inputT (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))) S Rw B
        (RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length) v (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode (j+1))) (layoutAt (j+1)) (factsAt (j+1))).length i)) ∧
      InvR e hV Rc Rk K K0 KH0 (j+1) w q Mb Ms cW cQ cB cS S Rw B v U0 fuel' H' A' ∧
      (∀ kk : Fin 13, H' (Dims.encT (d := 𝔇) hV kk) = Hout (Dims.encT (d := 𝔇) hV kk)) ∧
      A' (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^q))) ∧
      (∀ hm : j + 1 < (monomials coordinate ph ci).length, ∀ i : Fin 3,
        A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[j+1]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      (∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) → A' (Dims.encT (d := 𝔇) hV kk) =
        ZeroPadding.pad (reserve (Dims.encT (d := 𝔇) hV kk))
          (install app (install enc Aj E) T (Dims.encT (d := 𝔇) hV kk))) ∧
      (∀ x : Fin V, x.val < (𝔇).F → Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV)
          ((𝔇).poolSlots hV) ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x →
        H' x = Hout x ∧ A' x = install app (install enc Aj E) T x) ∧
      (∀ i : Fin 3, (A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  classical
  obtain ⟨H3, A3, Av3, realRun, hM3, ⟨res3⟩, e4, e02, ecs1, ecs2, edrv0, edrv1, edrv2, edrv4, hwork3, hcsH, hdrvH,
      hfam3, ⟨ecurT, ecurTH⟩, ⟨a11, h11, a12, h12⟩, ⟨a10z, h10z, a11z, h11z⟩, fr3, dirt3, dirtZ3, encH3, e02L⟩ :=
    refill_pro5_run mask packets rows sources res p k r se sp e hV g7M g7cost coordinate ph ci L target mode Rc Rk b
      layoutAt capsAt K K0 KH0 hG7 slots hslots enc app hencP happP reserve hreserve fm n Hj Hout Aj Y E T hHout j hj hRc
      hRk w cW cQ Mb Ms cB cS S Rw B v U0 hInv hcW hcQ hcB hcS hSl hRl hBl hvl hUl hMb hMs hKpos hKpad hKapp henc0 hlog
      he1 hpw hfirst hsecond
  clear hlog he1 hpw hfirst hsecond henc0 hG7
  obtain ⟨c0, hc0⟩ : ∃ c0 : Nat, c0 = (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) := ⟨_, rfl⟩
  obtain ⟨rc, hrc⟩ : ∃ rc : Nat, rc = (restCost se sp g7cost (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms j) := ⟨_, rfl⟩
  have wI : cursorCost j + 1 + g7cost (j+1) + 1 + c0 + 1 ≤ Rc := by rw [hc0]; exact hwinI
  have wZ : rc + 1 + c0 + 1 ≤ Rk := by rw [hc0, hrc]; exact hwinZ
  clear hwinI hwinZ
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  have hres2 := e.ext2.hres2
  have hres3 := e.hres3
  have hF := e.ext2.ext1.ext.hF
  have vrs : ∀ i : Fin 5, ((𝔇).rsT e.ext2.ext1 hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + i.val :=
    fun _ => rfl
  have vmT : ∀ i : Fin 5, (Dims.mT e.ext2 hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + 5 + i.val :=
    fun _ => rfl
  have vrf : ∀ i : Fin 5, (Dims.rfT e.ext2 hV i).val = (𝔇).B + 14 + i.val := fun _ => rfl
  have vscr : ∀ m : Fin 13, ((𝔇).scr hV m).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val := fun _ => rfl
  have vhr : ∀ i : Fin 12, (Dims.hrT e hV i).val = (𝔇).B + 29 + restPc se.extra sp.extra gW + i.val := fun _ => rfl
  have venc : ∀ kk : Fin 13, (Dims.encT (d := 𝔇) hV kk).val = (𝔇).F + (𝔇).rt + kk.val := fun _ => rfl
  have vcs1 : (Dims.csSlots e.ext2.ext1.ext hV 1).val = (𝔇).B + 13 := rfl
  have vcs2 : (Dims.csSlots e.ext2.ext1.ext hV 2).val = (𝔇).B + 14 := rfl
  have vd0 : (Dims.drvSlots e.ext2.ext1.ext hV 0).val = (𝔇).B + 15 := rfl
  have vd1 : (Dims.drvSlots e.ext2.ext1.ext hV 1).val = (𝔇).B + 16 := rfl
  have vd2 : (Dims.drvSlots e.ext2.ext1.ext hV 2).val = (𝔇).B + 17 := rfl
  have vd4 : (Dims.drvSlots e.ext2.ext1.ext hV 4).val = (𝔇).B + 18 := rfl
  let amb : Fin V → List Bool := fun x => ZeroPadding.pad (reserve x) (install app (install enc Aj E) T x)
  have ambHigh : ∀ x : Fin V, (𝔇).G ≤ x.val → amb x = ZeroPadding.pad Rc (Aj x) := by
    intro x hx
    have ha : ∀ i, app i ≠ x := fun i h => by
      have := happP i; have := congrArg Fin.val h; omega
    have he : ∀ i, enc i ≠ x := fun i h => by
      have := hencP i; have := congrArg Fin.val h; omega
    show ZeroPadding.pad (reserve x) (install app (install enc Aj E) T x) = _
    rw [hreserve x, if_pos (show (𝔇).F ≤ x.val by omega), install_other app _ _ x ha, install_other enc _ _ x he]
  have ambLow : ∀ x : Fin V, x.val < (𝔇).F → (∀ i, app i ≠ x) → amb x = Aj x := by
    intro x hx ha
    have he : ∀ i, enc i ≠ x := fun i h => by
      have := hencP i; have := congrArg Fin.val h; omega
    show ZeroPadding.pad (reserve x) (install app (install enc Aj E) T x) = _
    rw [hreserve x, if_neg (show ¬ (𝔇).F ≤ x.val by omega), ZeroPadding.pad_zero, install_other app _ _ x ha,
      install_other enc _ _ x he]
  have houtNS : ∀ x : Fin V, (x.val < (𝔇).F ∨ (𝔇).F + (𝔇).rt ≤ x.val) → Hout x = Hj x := by
    intro x hx
    apply hHout
    intro i h
    have := i.isLt; have := hslots i; have := congrArg Fin.val h
    omega
  have hiZ : ∀ x : Fin V, (x.val < (𝔇).B + 19 ∨ (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val) →
      ¬ (𝔇).InZ se.extra sp.extra x.val := by
    intro x hx hz; unfold SourceConstruction.Dims.InZ at hz; rw [vPc] at hx; omega
  have encNZ : ∀ kk : Fin 13, ¬ (𝔇).InZ se.extra sp.extra (Dims.encT (d := 𝔇) hV kk).val := fun kk =>
    hiZ _ (Or.inl (by rw [venc]; omega))
  -- 1. the cycle from the lifted prologue exit
  have hres19 : 19 ≤ res := by
    have : (𝔇).res = res := rfl
    omega
  have wi := wiring mask packets rows sources res p k r hres19 hV
  have hA1low : ∀ x : Fin V, ¬ (𝔇).InZ se.extra sp.extra x.val →
      ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk x) (A3 x) = A3 x := by
    intro x hz; simp only [SourceConstruction.Dims.capZ, if_neg hz, ZeroPadding.pad_zero]
  have A1eq : ∀ x : Fin V, x.val < (𝔇).B + 19 →
      (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) x = A3 x :=
    fun x hx => hA1low x (hiZ x (Or.inl hx))
  have hMZ : ∀ x, (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) x =
      ZeroPadding.pad ((𝔇).RZ se.extra sp.extra gW Rc Rk x) (Av3 x) := by
    intro x
    show ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk x) (A3 x) = _
    rw [hM3 x, Uniform.pad_pad]
    simp only [SourceConstruction.Dims.capZ, SourceConstruction.Dims.RZ, Dims.Rpad]
    by_cases hz : (𝔇).InZ se.extra sp.extra x.val
    · rw [if_pos hz, if_pos hz, if_pos (Dims.InZ_clear (gW := gW) hz), max_eq_left hRk]
    · rw [if_neg hz, if_neg hz, Nat.zero_max]
  have hRZ1 : (𝔇).RZ se.extra sp.extra gW Rc Rk (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = 0 := by
    have hv : (Dims.rewind2Slots e.ext2.ext1.ext hV 1).val = 278 := rfl
    have hz1 : ¬ (𝔇).InZ se.extra sp.extra (Dims.rewind2Slots e.ext2.ext1.ext hV 1).val := by
      unfold SourceConstruction.Dims.InZ; rw [hv]; omega
    have hc1 : ¬ (𝔇).InClear se.extra sp.extra gW (Dims.rewind2Slots e.ext2.ext1.ext hV 1).val := by
      unfold SourceConstruction.Dims.InClear; rw [hv]; omega
    simp only [SourceConstruction.Dims.RZ, Dims.Rpad, if_neg hz1, if_neg hc1]
  have hRZ2 : (𝔇).RZ se.extra sp.extra gW Rc Rk (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = 0 := by
    have hv : (Dims.rewind2Slots e.ext2.ext1.ext hV 2).val = 279 := rfl
    have hz1 : ¬ (𝔇).InZ se.extra sp.extra (Dims.rewind2Slots e.ext2.ext1.ext hV 2).val := by
      unfold SourceConstruction.Dims.InZ; rw [hv]; omega
    have hc1 : ¬ (𝔇).InClear se.extra sp.extra gW (Dims.rewind2Slots e.ext2.ext1.ext hV 2).val := by
      unfold SourceConstruction.Dims.InClear; rw [hv]; omega
    simp only [SourceConstruction.Dims.RZ, Dims.Rpad, if_neg hz1, if_neg hc1]
  have csHigh : ∀ kk : Fin 16, 4 ≤ kk.val → (Dims.csSlots e.ext2.ext1.ext hV kk).val = (𝔇).B + (kk.val - 3) := by
    intro kk hk
    simp only [Dims.csSlots, Dims.csV]
    split_ifs <;> omega
  have famRes : ∀ i : Fin (𝔇).R1, i.val ≠ 0 → i.val ≠ 262 →
      SourceRequest.famReserve res3 ((𝔇).RZ se.extra sp.extra gW Rc Rk) i = Rc := by
    intro i h0 h262
    have hin := fam_in mask packets rows sources res p k r (eX := se.extra) (pX := sp.extra) (gW := gW) hV i
    have hnz : ¬ (𝔇).InZ se.extra sp.extra ((𝔇).familySlots hV i).val := by
      intro hz; unfold SourceConstruction.Dims.InZ at hz
      have := i.isLt; have := (𝔇).hsp
      simp only [SourceConstruction.Dims.familySlots, SourceConstruction.Dims.famV] at hz
      split_ifs at hz <;> omega
    have hb := res3.b_family i h0 h262
    have hlen := (dirt3 _ (Or.inl hin) hnz).1
    rw [hM3, hb] at hlen
    simp only [Dims.Rpad, if_pos hin, ZeroPadding.pad, List.length_append, List.length_replicate] at hlen
    simp only [SourceRequest.famReserve, if_neg h0, if_neg h262, SourceConstruction.Dims.RZ, if_neg hnz, Dims.Rpad,
      if_pos hin]
    exact max_eq_left (by omega)
  have hcnt := famRes (Fin.last _) (Cycle.last_val (rows (decompositionOf sources) (printerOf sources))).1 (Cycle.last_val (rows (decompositionOf sources) (printerOf sources))).2
  have hdesc : max (SourceRequest.famReserve res3 ((𝔇).RZ se.extra sp.extra gW Rc Rk)
      (SLoad.Final.port (printerOf sources) (rows (decompositionOf sources) (printerOf sources)))) (capsAt (j+1)).descriptorReserve = Rc := by
    rw [famRes _ (Cycle.port_val (rows (decompositionOf sources) (printerOf sources))).1 (Cycle.port_val (rows (decompositionOf sources) (printerOf sources))).2]
    exact max_eq_left hdescR
  obtain ⟨H', A', conj1, conj2, fH, fA, frC, rw1H, rw1A, rw2H, rw2A⟩ := Cycle.cycle_prepared_pad_rw mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
    ((𝔇).maskSlots hV) hminj ((𝔇).pslots hV) hsinj ((𝔇).slot hV) ((𝔇).ret hV)
    ((𝔇).scr hV 0) ((𝔇).scr hV 1) ((𝔇).scr hV 2) ((𝔇).scr hV 3) ((𝔇).scr hV 4) ((𝔇).familySlots hV) hfinj
    ((𝔇).poolSlots hV) hpinj (Dims.rewind2Slots e.ext2.ext1.ext hV) hrinj hraw hpool hsrc
    ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
    (Dims.lenTape e.ext2.ext1.ext hV) (refillPro3 se sp e hV g7M) (Dims.csSlots e.ext2.ext1.ext hV) (Dims.natSlots hV)
    (Dims.drvSlots e.ext2.ext1.ext hV) wi H3 (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) Av3
    ((𝔇).RZ se.extra sp.extra gW Rc Rk) hMZ (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1))
    (goodAt (j+1)) res3 hRZ1 hRZ2 (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 Rc S Rw B v
    ((A1eq _ (by rw [vcs1]; omega)).trans ecs1)
    ((A1eq _ (by rw [vcs2]; omega)).trans ecs2)
    (fun kk hk => (A1eq _ (by rw [csHigh kk hk]; have := kk.isLt; omega)).trans (hwork3 kk hk))
    hcsH
    ((A1eq _ (by rw [vd0]; omega)).trans edrv0) ((A1eq _ (by rw [vd1]; omega)).trans edrv1)
    ((A1eq _ (by rw [vd2]; omega)).trans edrv2) ((A1eq _ (by rw [vd4]; omega)).trans edrv4) hdrvH
    (fun i _ => (A1eq _ (by
      have hrt : (𝔇).rt = r_tapes (printerOf sources) := rfl
      simp only [Dims.natSlots]; have := i.isLt; omega)).trans (hfam3 i).1)
    (fun i _ => (hfam3 i).2)
    hcnt hdesc hL
  have sH : Step _ (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (factsAt (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) H3 (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) H' A' :=
    Cycle.prepared_step _ _ _ _ _ _ _ conj2
  have hP := fun z hfam => Refill.prepared_mono _ _ hcost (conj1 _ _ _ (realRun z hfam))
  clear hcost conj1 conj2 realRun hdescR hL famRes hcnt hdesc hMZ hRZ1 hRZ2 wi
  -- 2. the exit facts: frames through the cycle, the lift and the prologue
  have toA3 : ∀ x : Fin V, Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).poolSlots hV)
        ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x →
      (x.val < (𝔇).F ∨ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val < (𝔇).G) ∨ (𝔇).B + 18 < x.val ∨
        ((𝔇).G + (𝔇).R1 ≤ x.val ∧ x.val < (𝔇).B)) →
      ¬ (𝔇).InZ se.extra sp.extra x.val → A' x = A3 x ∧ H' x = H3 x := by
    intro x hf hx hz
    obtain ⟨o1, o2, o3⟩ := off_cycle e.ext2.ext1.ext hV x hx
    obtain ⟨a, b⟩ := frC x hf o1 o2 o3
    exact ⟨b.trans (hA1low x hz), a⟩
  have keepAll : ∀ x : Fin V, Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).poolSlots hV)
        ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x →
      (x.val < (𝔇).F ∨ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val < (𝔇).G) ∨
        (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val) →
      ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
      x ≠ (𝔇).rsT e.ext2.ext1 hV 2 → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
      A' x = amb x ∧ H' x = Hout x := by
    intro x hf hlo henc h2 h10 h11
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := frame_region e hV x hlo
    obtain ⟨a1, a2⟩ := toA3 x hf c7 c5
    obtain ⟨b1, b2⟩ := fr3 x c1 c2 c3 c4 h2 henc c6 h10 h11
    exact ⟨a1.trans b1, a2.trans b2⟩
  have encA3 : ∀ kk : Fin 13, A' (Dims.encT (d := 𝔇) hV kk) = A3 (Dims.encT (d := 𝔇) hV kk) ∧
      H' (Dims.encT (d := 𝔇) hV kk) = H3 (Dims.encT (d := 𝔇) hV kk) := fun kk =>
    toA3 _ (free_mid e.ext2.ext1.ext hV _ (enc_region e hV kk).1 (enc_region e hV kk).2.1)
      (Or.inr (Or.inl ⟨(enc_region e hV kk).1, (enc_region e hV kk).2.1⟩)) (encNZ kk)
  refine ⟨H', A', hP, fH, fA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `InvR (j+1)`
    have rsNe2 : ∀ i : Fin 5, i ≠ 2 → (𝔇).rsT e.ext2.ext1 hV i ≠ (𝔇).rsT e.ext2.ext1 hV 2 := fun i hi h =>
      hi (Dims.rsT_injective e.ext2.ext1 hV h)
    have mNe2 : ∀ i : Fin 5, Dims.mT e.ext2 hV i ≠ (𝔇).rsT e.ext2.ext1 hV 2 := fun i h => by
      have := congrArg Fin.val h; rw [vmT, vrs] at this; omega
    have rsH19 : ∀ i : Fin 5, (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ ((𝔇).rsT e.ext2.ext1 hV i).val :=
      fun i => Nat.le_add_right _ _
    have mH19 : ∀ i : Fin 5, (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ (Dims.mT e.ext2 hV i).val :=
      fun i => le_trans (Nat.le_add_right _ 5) (Nat.le_add_right _ _)
    have resid : ∀ x : Fin V, (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val → x ≠ (𝔇).rsT e.ext2.ext1 hV 2 →
        x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 → A' x = ZeroPadding.pad Rc (Aj x) ∧ H' x = Hj x := by
      intro x hx h2 h10 h11
      obtain ⟨g1, _, g3, g4, g5, _⟩ := high_region x hx
      obtain ⟨a1, a2⟩ := keepAll x (Dims.free_res e.ext2.ext1.ext hV x g4) (Or.inr (Or.inr hx)) g5 h2 h10 h11
      rw [a1, a2, ambHigh x g1, houtNS x (Or.inr g3)]
      exact ⟨rfl, rfl⟩
    have sc : ∀ m : Fin 13, 5 ≤ m.val → A' ((𝔇).scr hV m) = A3 ((𝔇).scr hV m) ∧
        H' ((𝔇).scr hV m) = H3 ((𝔇).scr hV m) := fun m hm =>
      toA3 _ (free_scr mask packets rows sources res p k r e.ext2.ext1.ext hV m hm)
        (Or.inr (Or.inr (Or.inr (by rw [vscr]; omega)))) (hiZ _ (Or.inl (by rw [vscr]; omega)))
    have curA := toA3 ((𝔇).rsT e.ext2.ext1 hV 2) (Dims.free_res e.ext2.ext1.ext hV _ (high_region _ (rsH19 2)).2.2.2.1)
      (Or.inr (Or.inr (Or.inl (by rw [vrs]; omega)))) (hiZ _ (Or.inr (rsH19 2)))
    have hrA : ∀ i : Fin 12, A' (Dims.hrT e hV i) = A3 (Dims.hrT e hV i) ∧ H' (Dims.hrT e hV i) = H3 (Dims.hrT e hV i) :=
      fun i => toA3 _ (Dims.hrT_free e hV i) (Or.inr (Or.inr (Or.inl (by rw [vhr]; omega)))) (Dims.hrT_notZ e hV i)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · 
      intro x hx
      rcases hKfree x hx with hfx | hr1 | hr2
      · rcases hKpos x hx with hl | ⟨hh, h10, h11⟩
        · obtain ⟨l1, l2, l3, _, l5⟩ := low_region e hV x hl
          obtain ⟨a1, a2⟩ := keepAll x hfx (Or.inl hl) l3 l1 (l2 10) (l2 11)
          rw [a1, a2, ambLow x hl (hKapp x hx), houtNS x l5]
          exact hInv.kept x hx
        · obtain ⟨k1, k2⟩ := kept_high e hV x hh
          obtain ⟨g1, g2, g3, _, g5, _⟩ := high_region x k1
          obtain ⟨a1, a2⟩ := keepAll x hfx (Or.inr (Or.inr k1)) g5 k2 h10 h11
          rw [a1, a2, ambHigh x g1, houtNS x (Or.inr g3), (hInv.kept x hx).1, (hInv.kept x hx).2, hKpad x hx g2]
          exact ⟨rfl, rfl⟩
      · subst hr1
        exact ⟨rw1A.trans (hKr1 hx).1.symm, rw1H.trans (hKr1 hx).2.symm⟩
      · subst hr2
        exact ⟨rw2A.trans (hKr2 hx).1.symm, rw2H.trans (hKr2 hx).2.symm⟩
    · exact curA.1.trans ecurT
    · rw [(resid _ (rsH19 _) (rsNe2 0 (by decide)) (Ne.symm (Dims.hrT_ne_rsT e hV 10 0))
        (Ne.symm (Dims.hrT_ne_rsT e hV 11 0))).1, hInv.big]; exact pad_over _ _ hcB _
    · rw [(resid _ (rsH19 _) (rsNe2 1 (by decide)) (Ne.symm (Dims.hrT_ne_rsT e hV 10 1))
        (Ne.symm (Dims.hrT_ne_rsT e hV 11 1))).1, hInv.small]; exact pad_over _ _ hcS _
    · rw [(resid _ (rsH19 _) (rsNe2 3 (by decide)) (Ne.symm (Dims.hrT_ne_rsT e hV 10 3))
        (Ne.symm (Dims.hrT_ne_rsT e hV 11 3))).1, hInv.wv]; exact pad_over _ _ hcW _
    · rw [(resid _ (rsH19 _) (rsNe2 4 (by decide)) (Ne.symm (Dims.hrT_ne_rsT e hV 10 4))
        (Ne.symm (Dims.hrT_ne_rsT e hV 11 4))).1, hInv.qv]; exact pad_over _ _ hcQ _
    · intro i
      by_cases h2 : i = 2
      · subst h2; exact curA.2.trans ecurTH
      · rw [(resid _ (rsH19 _) (rsNe2 i h2) (Ne.symm (Dims.hrT_ne_rsT e hV 10 i))
          (Ne.symm (Dims.hrT_ne_rsT e hV 11 i))).2]; exact hInv.rsH i
    · rw [(resid _ (mH19 _) (mNe2 0) (Ne.symm (Dims.hrT_ne_mT e hV 10 0))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 0))).1, hInv.mU]; exact pad_same _ _
    · rw [(resid _ (mH19 _) (mNe2 1) (Ne.symm (Dims.hrT_ne_mT e hV 10 1))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 1))).1, hInv.mS]; exact pad_same _ _
    · rw [(resid _ (mH19 _) (mNe2 2) (Ne.symm (Dims.hrT_ne_mT e hV 10 2))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 2))).1, hInv.mR]; exact pad_same _ _
    · rw [(resid _ (mH19 _) (mNe2 3) (Ne.symm (Dims.hrT_ne_mT e hV 10 3))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 3))).1, hInv.mB]; exact pad_same _ _
    · rw [(resid _ (mH19 _) (mNe2 4) (Ne.symm (Dims.hrT_ne_mT e hV 10 4))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 4))).1, hInv.mv]; exact pad_same _ _
    · intro i
      rw [(resid _ (mH19 _) (mNe2 i) (Ne.symm (Dims.hrT_ne_mT e hV 10 i))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 i))).2]; exact hInv.mH i
    · exact (sc 11 (by decide)).1.trans a11
    · exact (sc 11 (by decide)).2.trans h11
    · exact (sc 12 (by decide)).1.trans a12
    · exact (sc 12 (by decide)).2.trans h12
    · exact (hrA 10).1.trans a10z
    · exact (hrA 10).2.trans h10z
    · exact (hrA 11).1.trans a11z
    · exact (hrA 11).2.trans h11z
    · -- dirt off `Z`: length (cycle dirt over the Rc-free prologue heads, `hwinI`)
      intro x hx hz
      obtain ⟨d1, d2⟩ := dirt3 x hx hz
      have b1 := (dirty_bound sH x).1
      have e1 := hA1low x hz
      simp only [e1] at b1
      rw [← hc0] at b1
      omega
    · intro x hx hz
      obtain ⟨_, d2⟩ := dirt3 x hx hz
      have b2 := (dirty_bound sH x).2
      rw [← hc0] at b2
      omega
    · -- the family bank: the next family input heads (`hfamH`)
      intro x h1 h2
      have hx : x = Dims.natSlots hV ⟨x.val - (𝔇).F, by omega⟩ := Fin.ext (by simp only [Dims.natSlots]; omega)
      rw [hx, fH]
      exact hfamH _
    · -- `Z` at the outer capacity (`hwinZ`)
      intro x hz
      obtain ⟨d1, d2⟩ := dirtZ3 x hz
      have b1 := (dirty_bound sH x).1
      have e1 : ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk x) (A3 x) = ZeroPadding.pad Rk (A3 x) := by
        simp only [SourceConstruction.Dims.capZ, if_pos hz]
      simp only [e1, pad_len_max] at b1
      rw [← hc0] at b1
      rw [← hrc] at d1 d2
      omega
    · intro x hz
      obtain ⟨_, d2⟩ := dirtZ3 x hz
      have b2 := (dirty_bound sH x).2
      rw [← hc0] at b2
      rw [← hrc] at d2
      omega
    · intro kk hk
      rw [(encA3 kk).2, encH3 kk, houtNS _ (Or.inr (by rw [venc]; omega))]
      exact hInv.encH kk hk
  · -- (E1)
    intro kk
    exact (encA3 kk).2.trans (encH3 kk)
  · -- (E2) the denominator word
    exact (encA3 4).1.trans e4
  · -- (E2) the coefficient words
    intro hm i
    exact (encA3 _).1.trans (e02 hm i)
  · -- (E3) the other `encT` tapes
    intro kk hk
    obtain ⟨n1, n2, n3, n4, n5⟩ := enc_region e hV kk
    exact (keepAll _ (free_mid e.ext2.ext1.ext hV _ n1 n2) (Or.inr (Or.inl ⟨n1, n2⟩)) (n5 hk) n3 (n4 10) (n4 11)).1
  · -- (E3) every `Free` tape below `F`
    intro x hx hf
    obtain ⟨l1, l2, l3, _, _⟩ := low_region e hV x hx
    obtain ⟨a1, a2⟩ := keepAll x hf (Or.inl hx) l3 l1 (l2 10) (l2 11)
    refine ⟨a2, a1.trans ?_⟩
    show ZeroPadding.pad (reserve x) _ = _
    rw [hreserve x, if_neg (Nat.not_le.mpr hx), ZeroPadding.pad_zero]
  · 
    intro i
    rw [(encA3 _).1]
    exact e02L i

end concrete

end Rest
end
end NearCubicWires.SourceConstruction
end
