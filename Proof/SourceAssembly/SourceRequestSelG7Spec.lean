import Proof.SourceAssembly.SourceRequestSelHG7Site
import Proof.SourceAssembly.SourceFactorSelG7Fam

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
namespace NearCubicWires.SourceRequest.SelG7Spec
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

def g7costW (sources : EightSources) (mask : MaskProducer) (MB : List Bool) (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output rq).clauseBits))
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (bits : List Bool) (ph : CloseoutRowsOriginalSchedule.Phase) (L target cwid cw D b Pw W Ld : Nat) : Bool → Nat → Nat
  | false => Item4.g7Cost (fun m => SelLocal.selThrCost a rq ci coordinate bits ph L target cwid cw D b m)
      (fun m => Words.wordsCost mask (NearCubicWires.SourceStart.Bank.sb (decompositionOf sources)) (requestAt coordinate ph ci L target false m) MB)
      (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) coordinate ph ci L target
  | true => Item4.g7Cost (fun m => SelLocal.selSymCost a rq ci coordinate bits ph L target cwid cw D b m)
      (fun m => Words.wordsCost mask (NearCubicWires.SourceStart.Bank.sb (decompositionOf sources)) (requestAt coordinate ph ci L target true m) MB)
      (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) coordinate ph ci L target

theorem kb_le (sources : EightSources) : G7Fam.kb sources ≤ 512 := by
  show 194 ≤ 512
  decide

section site
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔡" => NearCubicWires.SourceSkeleton.FirstW.dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇" => NearCubicWires.SourceSkeleton.FirstW.dSite selector xtra mask packets rows sources gamma hg hh p

theorem g7Spec (mode : Bool) {V : Nat} (hV : (𝔡).U ≤ V)
    (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (L target : Nat) (Rc b qCap : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps) (MB : List Bool) (dR : Nat)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (Pw W Ld : Nat) (bits : List Bool) (hread : SourceRequest.CoordBridge.CoordReads mode coordinate bits)
    (cwid cw D c QK : Nat) (pw : List Bool)
    (hKc : ∀ j, K ((NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode) j) ∧ K0 ((NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode) j) = PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity ci.val
      (PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)) pw j ∧ KH0 ((NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV mode) j) = 0)
    (hKw : ∀ x : Fin V, x.val = 1 → K x ∧ K0 x = RepairOrdinary.frame bits ∧ KH0 x = 0)
    (hKr : ∀ i, i < 10 → ∀ x : Fin V, x.val = (𝔇).B + 29 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW + i →
      K x ∧ K0 x = ZeroPadding.pad Rc ((if mode then resWS else resW) rq.arity Pw W Ld L target cwid cw i) ∧ KH0 x = 0)
    (hKD : ∀ x : Fin V, x.val = (𝔇).B + 41 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate D true) ∧ KH0 x = 0)
    (hKt : K (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV) ∧ K0 (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV) = ZeroPadding.pad QK (List.replicate (2 ^ (a.output rq).clauseBits) true) ∧
      KH0 (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV) = 0)
    (hKb : ∀ x : Fin V, x.val = (𝔇).B + 48 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate b true) ∧ KH0 x = 0)
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
    (hcwid : cwid = if mode then SymOriginal.symCodeWidth Ld else ThrSwitch.codeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left).val ∨
      jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : rq.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : ∀ m, m ≤ (FactorLoop.monomials coordinate ph ci).length →
      SourceFactorSel.HdrBlock.Fits mode rq.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (Vb : Nat) (hV4 : 4 ≤ Vb)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hbigR : SourceFactorSel.CoefR.coefBigR Vb (2 ^ (a.output rq).clauseBits) b (cw + rhoW) ≤ Rc)
    (hcap : if mode then (∀ j, ∀ mo ∈ (coordinate j).monomials, ∀ cc,
      RepairSource.CloseoutFinal.C10TotalDecode.Atom.symmetric cc ∈ mo.factors →
      4 ≤ Ld ∧ cc.descriptionBits ≤ Ld ∧ cc.wireCount ≤ W ∧
        CloseoutRowsCircuitCapacity.capacity (SourceRequest.SymOriginal.symCodeWidth Ld) ≤ Pw)
      else (∀ j, ∀ mo ∈ (coordinate j).monomials, ∀ cc,
      RepairSource.CloseoutFinal.C10TotalDecode.Atom.threshold cc ∈ mo.factors →
      4 ≤ Ld ∧ cc.descriptionBits ≤ Ld ∧ cc.wireCount ≤ W ∧
        CloseoutRowsCircuitCapacity.capacity (SourceRequest.ThrSwitch.codeWidth Ld) ≤ Pw))
    (hRc1 : 1 ≤ Rc)
    (hKq : K (Dims.queryCopy (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV) ∧
      K0 (Dims.queryCopy (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV) = ZeroPadding.pad qCap (natListWord
        [RepairRepresentation.literalIndex ((a.output rq).clauses ci).left,
         RepairRepresentation.literalIndex ((a.output rq).clauses ci).right]) ∧ KH0 (Dims.queryCopy (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV) = 0)
    (hKres : ∀ m, m ≤ (monomials coordinate ph ci).length → ∀ x : Fin V,
      (𝔇).B + 43 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW ≤ x.val → x.val < (𝔇).B + 48 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (wd (decompositionOf sources) (requestAt coordinate ph ci L target mode m) MB
        (x.val - ((𝔇).B + 43 + restPc (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW) + 6)) ∧ KH0 x = 0)
    (hKrw : K (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV 1) ∧
      K0 (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV 1) = List.replicate dR true ∧ KH0 (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV 1) = 0 ∧
      K (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV 2) ∧
      K0 (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV 2) = List.replicate dR false ∧ KH0 (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV 2) = 0)
    (hMB : ∀ m, SLoad.Setup.metaBits (layoutAt m).w (layoutAt m).degree (layoutAt m).C (capsAt m) = MB)
    (hdR : ∀ m, (capsAt m).descriptorReserve = dR)
    (hNw : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * (requestAt coordinate ph ci L target mode m).nativeWord.length + 1 ≤ Rc)
    (hS : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).supportWord (decompositionOf sources)).length + 1 ≤ Rc)
    (hT : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).topWord (decompositionOf sources)).length + 1 ≤ Rc)
    (cq : ∀ m, m ≤ (monomials coordinate ph ci).length → 4 * (requestAt coordinate ph ci L target mode m).q + 3 ≤ Rc)
    (ck : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * normalizedLiveCount (requestAt coordinate ph ci L target mode m).q
        (requestAt coordinate ph ci L target mode m).liveScale + 3 ≤ Rc)
    (cm : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).occurrences.length + 3 ≤ Rc)
    (ci' : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).indexWord (decompositionOf sources)).length + 1 ≤ Rc)
    (hneed : ∀ m, m ≤ (monomials coordinate ph ci).length → ((NearCubicWires.SourceStart.Bank.sb (decompositionOf sources))).need (requestAt coordinate ph ci L target mode m) ≤ Rc)
    (cl1 : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).input (decompositionOf sources)).length + 1 ≤ Rc)
    (cl2 : 2 * MB.length + 1 ≤ Rc)
    (hwin : ∀ m, m ≤ (monomials coordinate ph ci).length →
      g7costW sources mask MB a rq ci coordinate bits ph L target cwid cw D b Pw W Ld mode m + 1 ≤ Rc) :
    ResidentRunH
      (G7Fam.g7At mask packets rows sources (NearCubicWires.SourceSkeleton.FirstW.resSite selector mask packets rows sources gamma hg hh p) p (NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p) (NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p) hV (NearCubicWires.SourceSkeleton.Params.gG7 sources gamma hg hh p)
        (fun md => NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV md) (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV)
        (SelHG7Site.hresSite selector xtra mask packets rows sources gamma hg hh p) (SelHG7Site.hNSite selector mask packets rows sources gamma hg hh p)
        (SelHG7Site.hNSiteS selector mask packets rows sources gamma hg hh p)
        (SelHG7Site.hroomSite selector mask packets rows sources gamma hg hh p (G7Fam.kb sources) (kb_le sources)) mode ph).2
      (g7costW sources mask MB a rq ci coordinate bits ph L target cwid cw D b Pw W Ld mode)
      mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra) (pX := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra) (gW := (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW) (V := V) Rc)
      (RestIn4 (𝔇) (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW Rc ((𝔇).pcT (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).se.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).sp.extra (NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p).gW x.val)  := by
  cases mode with
  | false =>
    rw [G7Fam.g7At_thr mask packets rows sources (NearCubicWires.SourceSkeleton.FirstW.resSite selector mask packets rows sources gamma hg hh p) p (NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p) (NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p)
      (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p) hV (NearCubicWires.SourceSkeleton.Params.gG7 sources gamma hg hh p)
      (fun md => NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV md) (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV)
      (SelHG7Site.hresSite selector xtra mask packets rows sources gamma hg hh p) (SelHG7Site.hNSite selector mask packets rows sources gamma hg hh p)
      (SelHG7Site.hNSiteS selector mask packets rows sources gamma hg hh p)
      (SelHG7Site.hroomSite selector mask packets rows sources gamma hg hh p (G7Fam.kb sources) (kb_le sources)) ph (a.output rq) Pw W Ld]
    exact SelHG7Site.hG7_site_thr selector xtra mask packets rows sources gamma hg hh p hV (NearCubicWires.SourceStart.Bank.sb (decompositionOf sources)) (fun _ => rfl) (kb_le sources) a rq coordinate ph ci L target Rc b qCap
      layoutAt capsAt MB dR K K0 KH0 Pw W Ld bits hread cwid cw D c QK pw hKc hKw hKr hKD hKt hKb hc hwinA hQR hiL hiR hcL hcR hbig hcwid h2cw
      hwinR hqD hPD hWD hLD hDR hDC hHfit hcw1 hcoef Vb hV4 hcoefV hbigR hcap hRc1 hKq hKres hKrw hMB hdR hNw hS hT cq ck cm ci' hneed cl1 cl2 hwin
  | true =>
    rw [G7Fam.g7At_sym mask packets rows sources (NearCubicWires.SourceSkeleton.FirstW.resSite selector mask packets rows sources gamma hg hh p) p (NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p) (NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p)
      (NearCubicWires.SourceSkeleton.FirstW.eSite selector xtra mask packets rows sources gamma hg hh p) hV (NearCubicWires.SourceSkeleton.Params.gG7 sources gamma hg hh p)
      (fun md => NearCubicWires.SourceSkeleton.FirstW.cacheSite selector xtra mask packets rows sources gamma hg hh p V hV md) (NearCubicWires.SourceSkeleton.FirstW.terminalSite selector xtra mask packets rows sources gamma hg hh p V hV)
      (SelHG7Site.hresSite selector xtra mask packets rows sources gamma hg hh p) (SelHG7Site.hNSite selector mask packets rows sources gamma hg hh p)
      (SelHG7Site.hNSiteS selector mask packets rows sources gamma hg hh p)
      (SelHG7Site.hroomSite selector mask packets rows sources gamma hg hh p (G7Fam.kb sources) (kb_le sources)) ph (a.output rq) Pw W Ld]
    exact SelHG7Site.hG7_site_sym selector xtra mask packets rows sources gamma hg hh p hV (NearCubicWires.SourceStart.Bank.sb (decompositionOf sources)) (fun _ => rfl) (kb_le sources) a rq coordinate ph ci L target Rc b qCap
      layoutAt capsAt MB dR K K0 KH0 Pw W Ld bits hread cwid cw D c QK pw hKc hKw hKr hKD hKt hKb hc hwinA hQR hiL hiR hcL hcR hbig hcwid h2cw
      hwinR hqD hPD hWD hLD hDR hDC hHfit hcw1 hcoef Vb hV4 hcoefV hbigR hcap hRc1 hKq hKres hKrw hMB hdR hNw hS hT cq ck cm ci' hneed cl1 cl2 hwin

end site

end
end NearCubicWires.SourceRequest.SelG7Spec
end

