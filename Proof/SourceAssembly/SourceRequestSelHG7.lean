import Proof.SourceAssembly.SourceRequestSelDockP
import Proof.SourceAssembly.SourceRequestSelOk
import Proof.SourceAssembly.SourceFactorSelItem4AtS

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
namespace NearCubicWires.SourceRequest.SelHG7
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

section S
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

theorem hG7_thr {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    (cacheT : Fin 19 → Fin V) (terminal : Fin V) (hresG : 49 + restPc eX pX gW ≤ (𝔇).res)
    (hN : SelFront.NF + (19 + 4 * SelLocal.tT (decompositionOf sources)) ≤ gW) (hG : SelFront.NF + (19 + 4 * SelLocal.tT (decompositionOf sources)) ≤ gG7)
    {kb : Nat} (SB : Item4.StartBank (decompositionOf sources) kb) (hIn : ∀ j, (SB.inPort j).val = j.val)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) kb ≤ gW)
    (hres48 : 48 + restPc eX pX gW ≤ (𝔇).res)
    (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (L target : Nat) (Rc b qCap : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target false m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target false m)))
    (capsAt : Nat → RowCaps) (MB : List Bool) (dR : Nat)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (Pw W Ld : Nat) (bits : List Bool) (hread : SourceRequest.CoordBridge.CoordReads false coordinate bits)
    (cwid cw D c QK : Nat) (pw : List Bool)
    (hKc : ∀ j, K (cacheT j) ∧ K0 (cacheT j) = PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity ci.val
      (PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)) pw j ∧ KH0 (cacheT j) = 0)
    (hKw : ∀ x : Fin V, x.val = 1 → K x ∧ K0 x = RepairOrdinary.frame bits ∧ KH0 x = 0)
    (hKr : ∀ i, i < 10 → ∀ x : Fin V, x.val = (𝔇).B + 29 + restPc eX pX gW + i →
      K x ∧ K0 x = ZeroPadding.pad Rc (resW rq.arity Pw W Ld L target cwid cw i) ∧ KH0 x = 0)
    (hKD : ∀ x : Fin V, x.val = (𝔇).B + 41 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate D true) ∧ KH0 x = 0)
    (hKt : K terminal ∧ K0 terminal = ZeroPadding.pad QK (List.replicate (2 ^ (a.output rq).clauseBits) true) ∧
      KH0 terminal = 0)
    (hKb : ∀ x : Fin V, x.val = (𝔇).B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate b true) ∧ KH0 x = 0)
    (hci : Function.Injective cacheT) (hcF : ∀ j, (cacheT j).val < (𝔇).F) (htF : terminal.val < (𝔇).F)
    (hc1 : ∀ j, (cacheT j).val ≠ 1) (hct : ∀ j, cacheT j ≠ terminal) (ht1 : terminal.val ≠ 1)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output rq).clauses ci).left)
      (index ((a.output rq).clauses ci).right) (negative ((a.output rq).clauses ci).left)
      (negative ((a.output rq).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity))
    (hwinA : litCost a rq ci (PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) + 1 ≤ Rc)
    (hiL : index ((a.output rq).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output rq).clauses ci).right + 3 ≤ Rc)
    (hcL : SourceFactorSel.CountRead.countCost bits (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left)).monomials.length
      (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right)).monomials.length ≤ Rc)
    (hcwid : cwid = ThrSwitch.codeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left).val ∨
      jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : rq.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : ∀ m, m ≤ (FactorLoop.monomials coordinate ph ci).length →
      SourceFactorSel.HdrBlock.Fits false rq.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (Vb : Nat) (hV4 : 4 ≤ Vb)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hbigR : SourceFactorSel.CoefR.coefBigR Vb (2 ^ (a.output rq).clauseBits) b (cw + rhoW) ≤ Rc)
    (hcapT : ∀ j, ∀ mo ∈ (coordinate j).monomials, ∀ cc,
      RepairSource.CloseoutFinal.C10TotalDecode.Atom.threshold cc ∈ mo.factors →
      4 ≤ Ld ∧ cc.descriptionBits ≤ Ld ∧ cc.wireCount ≤ W ∧
        CloseoutRowsCircuitCapacity.capacity (SourceRequest.ThrSwitch.codeWidth Ld) ≤ Pw)
    (hRc1 : 1 ≤ Rc)
    (hKq : K (Dims.queryCopy e.ext2.ext1.ext hV) ∧
      K0 (Dims.queryCopy e.ext2.ext1.ext hV) = ZeroPadding.pad qCap (natListWord
        [RepairRepresentation.literalIndex ((a.output rq).clauses ci).left,
         RepairRepresentation.literalIndex ((a.output rq).clauses ci).right]) ∧ KH0 (Dims.queryCopy e.ext2.ext1.ext hV) = 0)
    (hKres : ∀ m, m ≤ (monomials coordinate ph ci).length → ∀ x : Fin V,
      (𝔇).B + 43 + restPc eX pX gW ≤ x.val → x.val < (𝔇).B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (wd (decompositionOf sources) (requestAt coordinate ph ci L target false m) MB
        (x.val - ((𝔇).B + 43 + restPc eX pX gW) + 6)) ∧ KH0 x = 0)
    (hKrw : K (Dims.rewind2Slots e.ext2.ext1.ext hV 1) ∧
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = List.replicate dR true ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = 0 ∧
      K (Dims.rewind2Slots e.ext2.ext1.ext hV 2) ∧
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = List.replicate dR false ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = 0)
    (hMB : ∀ m, SLoad.Setup.metaBits (layoutAt m).w (layoutAt m).degree (layoutAt m).C (capsAt m) = MB)
    (hdR : ∀ m, (capsAt m).descriptorReserve = dR)
    (hNw : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * (requestAt coordinate ph ci L target false m).nativeWord.length + 1 ≤ Rc)
    (hS : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target false m).supportWord (decompositionOf sources)).length + 1 ≤ Rc)
    (hT : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target false m).topWord (decompositionOf sources)).length + 1 ≤ Rc)
    (cq : ∀ m, m ≤ (monomials coordinate ph ci).length → 4 * (requestAt coordinate ph ci L target false m).q + 3 ≤ Rc)
    (ck : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * normalizedLiveCount (requestAt coordinate ph ci L target false m).q
        (requestAt coordinate ph ci L target false m).liveScale + 3 ≤ Rc)
    (cm : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * ((requestAt coordinate ph ci L target false m).family (decompositionOf sources)).occurrences.length + 3 ≤ Rc)
    (ci' : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target false m).indexWord (decompositionOf sources)).length + 1 ≤ Rc)
    (hneed : ∀ m, m ≤ (monomials coordinate ph ci).length → SB.need (requestAt coordinate ph ci L target false m) ≤ Rc)
    (cl1 : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target false m).input (decompositionOf sources)).length + 1 ≤ Rc)
    (cl2 : 2 * MB.length + 1 ≤ Rc)
    (hwin : ∀ m, m ≤ (monomials coordinate ph ci).length →
      Item4.g7Cost (fun m => SelLocal.selThrCost a rq ci coordinate bits ph L target cwid cw D b m) (fun m => Words.wordsCost mask SB (requestAt coordinate ph ci L target false m) MB) (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) coordinate ph ci
        L target m + 1 ≤ Rc) :
    ResidentRunH
      (Item4.g7Machine (RecoveryFocus.machine (SelLocal.gS e hV (decompositionOf sources) cacheT terminal hresG hN) (SelLocal.selThrM ph (decompositionOf sources))) (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) (fun x => SelLocal.gS e hV (decompositionOf sources) cacheT terminal hresG hN (SelBack.rgP (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) x)) (wordsHostM (layS mask packets rows sources res p k r e hV gG7) SB (srcOf (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) (fun x => SelLocal.gS e hV (decompositionOf sources) cacheT terminal hresG hN (SelBack.rgP (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) x)))
        ((layS mask packets rows sources res p k r e hV gG7).hostV_lt _
          (layS_hN mask packets rows sources res p k r e hV gG7 kb hroom)
          (layS_hVB mask packets rows sources res p k r e hV gG7 hres48))))
      (Item4.g7Cost (fun m => SelLocal.selThrCost a rq ci coordinate bits ph L target cwid cw D b m) (fun m => Words.wordsCost mask SB (requestAt coordinate ph ci L target false m) MB) (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) coordinate ph ci
        L target)
      mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext2.ext1.ext hV) coordinate ph ci L target false Rc b
      ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := eX) (pX := pX) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) eX pX gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) eX pX gW x.val) := 
  AtS.hG7_of mask packets rows sources res p k r e hV gG7 SB hIn hroom hres48 coordinate ph ci L target false Rc b qCap
    layoutAt capsAt MB dR K K0 KH0 (RecoveryFocus.machine (SelLocal.gS e hV (decompositionOf sources) cacheT terminal hresG hN) (SelLocal.selThrM ph (decompositionOf sources)))
    (fun m => SelLocal.selThrCost a rq ci coordinate bits ph L target cwid cw D b m)
    (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld)
    (fun x => SelLocal.gS e hV (decompositionOf sources) cacheT terminal hresG hN (SelBack.rgP (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) x))
    (fun x y h => SelBack.rgP_inj _ x y (SelLocal.gS_inj e hV _ cacheT terminal hresG hN hci hcF htF hc1 hct ht1 h))
    (fun x => ∃ z : Fin SelFront.NF, 100 ≤ z.val ∧ SelLocal.gS e hV (decompositionOf sources) cacheT terminal hresG hN (SelBack.up z) = x)
    (SelLocal.selRun_SP e hV _ cacheT terminal hresG hN Pw W Ld a rq ci coordinate bits hread ph L target cwid cw D b Rc c qCap QK pw K K0 KH0
      hKc hKw hKr hKD hKt hKb hci hcF htF hc1 hct ht1 hc hwinA hQR hiL hiR hcL hcR hbig hcwid h2cw hwinR hqD hPD hWD hLD hDR hDC hHfit
      hcw1 hcoef Vb hV4 hcoefV hbigR)
    (SelLocal.gS_regR e hV _ cacheT terminal hresG hN Pw W Ld gG7 hG (a.output rq))
    (SelLocal.gS_scr e hV _ cacheT terminal hresG hN gG7 hG)
    (fun m hm i => SelLocal.ok_thr _ Pw W Ld coordinate bits hread ph ci hcapT m hm i)
    (fun m hm i => SelLocal.need_thr _ Pw W Ld Rc hRc1 _)
    hKq hKres hKrw hMB hdR hNw hS hT cq ck cm ci' hneed cl1 cl2 hwin

theorem hG7_sym {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    (cacheT : Fin 19 → Fin V) (terminal : Fin V) (hresG : 49 + restPc eX pX gW ≤ (𝔇).res)
    (hN : SelFront.NF + (19 + 4 * SelLocal.tS) ≤ gW) (hG : SelFront.NF + (19 + 4 * SelLocal.tS) ≤ gG7)
    {kb : Nat} (SB : Item4.StartBank (decompositionOf sources) kb) (hIn : ∀ j, (SB.inPort j).val = j.val)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) kb ≤ gW)
    (hres48 : 48 + restPc eX pX gW ≤ (𝔇).res)
    (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (L target : Nat) (Rc b qCap : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target true m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target true m)))
    (capsAt : Nat → RowCaps) (MB : List Bool) (dR : Nat)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (Pw W Ld : Nat) (bits : List Bool) (hread : SourceRequest.CoordBridge.CoordReads true coordinate bits)
    (cwid cw D c QK : Nat) (pw : List Bool)
    (hKc : ∀ j, K (cacheT j) ∧ K0 (cacheT j) = PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity ci.val
      (PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)) pw j ∧ KH0 (cacheT j) = 0)
    (hKw : ∀ x : Fin V, x.val = 1 → K x ∧ K0 x = RepairOrdinary.frame bits ∧ KH0 x = 0)
    (hKr : ∀ i, i < 10 → ∀ x : Fin V, x.val = (𝔇).B + 29 + restPc eX pX gW + i →
      K x ∧ K0 x = ZeroPadding.pad Rc (resWS rq.arity Pw W Ld L target cwid cw i) ∧ KH0 x = 0)
    (hKD : ∀ x : Fin V, x.val = (𝔇).B + 41 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate D true) ∧ KH0 x = 0)
    (hKt : K terminal ∧ K0 terminal = ZeroPadding.pad QK (List.replicate (2 ^ (a.output rq).clauseBits) true) ∧
      KH0 terminal = 0)
    (hKb : ∀ x : Fin V, x.val = (𝔇).B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate b true) ∧ KH0 x = 0)
    (hci : Function.Injective cacheT) (hcF : ∀ j, (cacheT j).val < (𝔇).F) (htF : terminal.val < (𝔇).F)
    (hc1 : ∀ j, (cacheT j).val ≠ 1) (hct : ∀ j, cacheT j ≠ terminal) (ht1 : terminal.val ≠ 1)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output rq).clauses ci).left)
      (index ((a.output rq).clauses ci).right) (negative ((a.output rq).clauses ci).left)
      (negative ((a.output rq).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity))
    (hwinA : litCost a rq ci (PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) + 1 ≤ Rc)
    (hiL : index ((a.output rq).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output rq).clauses ci).right + 3 ≤ Rc)
    (hcL : SourceFactorSel.CountRead.countCost bits (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left)).monomials.length
      (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right)).monomials.length ≤ Rc)
    (hcwid : cwid = SymOriginal.symCodeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left).val ∨
      jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : rq.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : ∀ m, m ≤ (FactorLoop.monomials coordinate ph ci).length →
      SourceFactorSel.HdrBlock.Fits true rq.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (Vb : Nat) (hV4 : 4 ≤ Vb)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hbigR : SourceFactorSel.CoefR.coefBigR Vb (2 ^ (a.output rq).clauseBits) b (cw + rhoW) ≤ Rc)
    (hcapS : ∀ j, ∀ mo ∈ (coordinate j).monomials, ∀ cc,
      RepairSource.CloseoutFinal.C10TotalDecode.Atom.symmetric cc ∈ mo.factors →
      4 ≤ Ld ∧ cc.descriptionBits ≤ Ld ∧ cc.wireCount ≤ W ∧
        CloseoutRowsCircuitCapacity.capacity (SourceRequest.SymOriginal.symCodeWidth Ld) ≤ Pw)
    (hRc1 : 1 ≤ Rc)
    (hKq : K (Dims.queryCopy e.ext2.ext1.ext hV) ∧
      K0 (Dims.queryCopy e.ext2.ext1.ext hV) = ZeroPadding.pad qCap (natListWord
        [RepairRepresentation.literalIndex ((a.output rq).clauses ci).left,
         RepairRepresentation.literalIndex ((a.output rq).clauses ci).right]) ∧ KH0 (Dims.queryCopy e.ext2.ext1.ext hV) = 0)
    (hKres : ∀ m, m ≤ (monomials coordinate ph ci).length → ∀ x : Fin V,
      (𝔇).B + 43 + restPc eX pX gW ≤ x.val → x.val < (𝔇).B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (wd (decompositionOf sources) (requestAt coordinate ph ci L target true m) MB
        (x.val - ((𝔇).B + 43 + restPc eX pX gW) + 6)) ∧ KH0 x = 0)
    (hKrw : K (Dims.rewind2Slots e.ext2.ext1.ext hV 1) ∧
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = List.replicate dR true ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = 0 ∧
      K (Dims.rewind2Slots e.ext2.ext1.ext hV 2) ∧
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = List.replicate dR false ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = 0)
    (hMB : ∀ m, SLoad.Setup.metaBits (layoutAt m).w (layoutAt m).degree (layoutAt m).C (capsAt m) = MB)
    (hdR : ∀ m, (capsAt m).descriptorReserve = dR)
    (hNw : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * (requestAt coordinate ph ci L target true m).nativeWord.length + 1 ≤ Rc)
    (hS : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target true m).supportWord (decompositionOf sources)).length + 1 ≤ Rc)
    (hT : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target true m).topWord (decompositionOf sources)).length + 1 ≤ Rc)
    (cq : ∀ m, m ≤ (monomials coordinate ph ci).length → 4 * (requestAt coordinate ph ci L target true m).q + 3 ≤ Rc)
    (ck : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * normalizedLiveCount (requestAt coordinate ph ci L target true m).q
        (requestAt coordinate ph ci L target true m).liveScale + 3 ≤ Rc)
    (cm : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * ((requestAt coordinate ph ci L target true m).family (decompositionOf sources)).occurrences.length + 3 ≤ Rc)
    (ci' : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target true m).indexWord (decompositionOf sources)).length + 1 ≤ Rc)
    (hneed : ∀ m, m ≤ (monomials coordinate ph ci).length → SB.need (requestAt coordinate ph ci L target true m) ≤ Rc)
    (cl1 : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target true m).input (decompositionOf sources)).length + 1 ≤ Rc)
    (cl2 : 2 * MB.length + 1 ≤ Rc)
    (hwin : ∀ m, m ≤ (monomials coordinate ph ci).length →
      Item4.g7Cost (fun m => SelLocal.selSymCost a rq ci coordinate bits ph L target cwid cw D b m) (fun m => Words.wordsCost mask SB (requestAt coordinate ph ci L target true m) MB) (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) coordinate ph ci
        L target m + 1 ≤ Rc) :
    ResidentRunH
      (Item4.g7Machine (RecoveryFocus.machine (SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hresG hN) (SelLocal.selSymM ph)) (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) (fun x => SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hresG hN (SelBack.rgP (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) x)) (wordsHostM (layS mask packets rows sources res p k r e hV gG7) SB (srcOf (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) (fun x => SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hresG hN (SelBack.rgP (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) x)))
        ((layS mask packets rows sources res p k r e hV gG7).hostV_lt _
          (layS_hN mask packets rows sources res p k r e hV gG7 kb hroom)
          (layS_hVB mask packets rows sources res p k r e hV gG7 hres48))))
      (Item4.g7Cost (fun m => SelLocal.selSymCost a rq ci coordinate bits ph L target cwid cw D b m) (fun m => Words.wordsCost mask SB (requestAt coordinate ph ci L target true m) MB) (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) coordinate ph ci
        L target)
      mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext2.ext1.ext hV) coordinate ph ci L target true Rc b
      ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := eX) (pX := pX) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) eX pX gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) eX pX gW x.val) := 
  AtS.hG7_of mask packets rows sources res p k r e hV gG7 SB hIn hroom hres48 coordinate ph ci L target true Rc b qCap
    layoutAt capsAt MB dR K K0 KH0 (RecoveryFocus.machine (SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hresG hN) (SelLocal.selSymM ph))
    (fun m => SelLocal.selSymCost a rq ci coordinate bits ph L target cwid cw D b m)
    (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld)
    (fun x => SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hresG hN (SelBack.rgP (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) x))
    (fun x y h => SelBack.rgP_inj _ x y (SelLocal.gSS_inj e hV _ cacheT terminal hresG hN hci hcF htF hc1 hct ht1 h))
    (fun x => ∃ z : Fin SelFront.NF, 100 ≤ z.val ∧ SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hresG hN (SelBack.up z) = x)
    (SelLocal.selRun_S_symP e hV _ cacheT terminal hresG hN Pw W Ld a rq ci coordinate bits hread ph L target cwid cw D b Rc c qCap QK pw K K0 KH0
      hKc hKw hKr hKD hKt hKb hci hcF htF hc1 hct ht1 hc hwinA hQR hiL hiR hcL hcR hbig hcwid h2cw hwinR hqD hPD hWD hLD hDR hDC hHfit
      hcw1 hcoef Vb hV4 hcoefV hbigR)
    (SelLocal.gSS_regR e hV _ cacheT terminal hresG hN Pw W Ld gG7 hG (a.output rq))
    (SelLocal.gSS_scr e hV _ cacheT terminal hresG hN gG7 hG)
    (fun m hm i => SelLocal.ok_sym _ Pw W Ld coordinate bits hread ph ci hcapS m hm i)
    (fun m hm i => SelLocal.need_sym _ Pw W Ld Rc hRc1 _)
    hKq hKres hKrw hMB hdR hNw hS hT cq ck cm ci' hneed cl1 cl2 hwin

end S

end
end NearCubicWires.SourceRequest.SelHG7
end

