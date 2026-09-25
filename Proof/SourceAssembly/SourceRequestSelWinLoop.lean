import Proof.SourceAssembly.SourceRequestSelWinSite

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
namespace NearCubicWires.SourceRequest.SelWinLoop
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
open NearCubicWires.SourceRequest.SelWinCore NearCubicWires.SourceRequest.SelWinSite
open NearCubicWires.SourceRequest.SelG7Spec (g7costW)
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes P1TopDown.WorkspaceSelectedAdmission.originalTapes
  P1TopDown.WorkspaceSelectedEntry.size RepairSource.SelectedRecoveryIntegration.outer

/-! ## 1. One `q`-slot for two `q`-summands -/

/-- Two `q`-power summands fit one: coefficient `c1 + c2`, exponent `max e1 e2`. -/
theorem merge_le (S c1 e1 c2 e2 : Nat) : c1 * (S + 1) ^ e1 + c2 * (S + 1) ^ e2 ≤ (c1 + c2) * (S + 1) ^ (max e1 e2) := by
  have h1 : (S + 1) ^ e1 ≤ (S + 1) ^ (max e1 e2) := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : (S + 1) ^ e2 ≤ (S + 1) ^ (max e1 e2) := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)

/-- **`q ≤ sqv q`** (the meta word's size scale `Sz q` starts with `q`, and `40·Sz ≤ ybv ≤ sqv`). -/
theorem q_le_sqv (selector : CyclicChoice.Laws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (Ccw Dcw CD DD r L target degree tg q : Nat) :
    q ≤ sqv selector sources p packets Ccw Dcw CD DD r L target degree tg q := by
  have h1 : q ≤ NearCubicWires.SourceStart.MetaCost.Sz selector sources p packets L q := by
    unfold NearCubicWires.SourceStart.MetaCost.Sz; omega
  have h2 : NearCubicWires.SourceStart.MetaCost.Sz selector sources p packets L q ≤ ybv selector sources p packets L degree tg q := by
    unfold ybv; omega
  have h3 := (sqv_ge selector sources p packets Ccw Dcw CD DD r L target degree tg q).2.2.2.2.2.2.2.2.1
  omega

/-! ## 2. The core, with the loop's `q`-part -/

/-- **`winCost` with the loop's `q`-part**: `hloop` has a second, `q`-sized summand `wCs·(Sq+1)^wEs`, merged into `Ebd`'s `q`-slot
(`wC + wCs`, `max wE wEs`). -/
theorem winCostQ (sources : EightSources) (mask : MaskProducer) (MB : List Bool) (a : PointwisePCPPAlgorithm)
    (rq : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (bits : List Bool) (ph : CloseoutRowsOriginalSchedule.Phase) (L target cwid cw D b Vb Pw W Ld n Sq cL dL wCs wEs : Nat)
    (mode : Bool) (m : Nat)
    (hbits : bits.length ≤ n)
    (hQ : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) ≤ Sq)
    (hJ : (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left)).monomials.length +
      (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right)).monomials.length + 1 ≤ Sq)
    (hcwidS : cwid ≤ Sq) (hcwS : cw ≤ Sq) (hDS : D ≤ Sq) (hLS : L ≤ Sq) (htS : target ≤ Sq) (hbS : b ≤ Sq) (hVbS : Vb ≤ Sq)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hY : WordsCost.Yb (decompositionOf sources) (requestAt coordinate ph ci L target mode m, MB) ≤ Sq)
    (hloop : loopW sources a rq ci coordinate ph L target Pw W Ld mode m ≤ cL * (n + 1) ^ dL + wCs * (Sq + 1) ^ wEs) :
    g7costW sources mask MB a rq ci coordinate bits ph L target cwid cw D b Pw W Ld mode m + 1 ≤
      Ebd n Sq cL dL (WordsCost.wC (decompositionOf sources) mask + wCs) (max (WordsCost.wE (decompositionOf sources) mask) wEs) := by
  rw [g7costW_eq]
  have hs := selW_le a rq ci coordinate bits ph L target cwid cw D b Vb Sq mode m hQ hJ hcwidS hcwS hDS hLS htS hbS hVbS hcw1
    hcoef hcoefV
  have hw := WordsCost.wordsCost_sb_le (decompositionOf sources) mask (requestAt coordinate ph ci L target mode m) MB
  have hw2 : WordsCost.wC (decompositionOf sources) mask *
        WordsCost.Yb (decompositionOf sources) (requestAt coordinate ph ci L target mode m, MB) ^ WordsCost.wE (decompositionOf sources) mask ≤
      WordsCost.wC (decompositionOf sources) mask * (Sq + 1) ^ WordsCost.wE (decompositionOf sources) mask :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hb : bits.length + 4 * Sq + 4 + 1 ≤ n + 1 + 4 * (Sq + 1) := by omega
  have hp : (bits.length + 4 * Sq + 4 + 1) ^ 24 ≤ (n + 1 + 4 * (Sq + 1)) ^ 24 := Nat.pow_le_pow_left hb 24
  have h1 : 1 ≤ (n + 1 + 4 * (Sq + 1)) ^ 24 := Nat.one_le_pow _ _ (by omega)
  have hmix := mixed n Sq 4 300000000000000000003 24
    (selW a rq ci coordinate bits ph L target cwid cw D b mode m + 3) (by decide) (by norm_num) (by decide) (by omega)
  have hm := merge_le Sq (WordsCost.wC (decompositionOf sources) mask) (WordsCost.wE (decompositionOf sources) mask) wCs wEs
  unfold Ebd
  have e2 : 2 ^ 200 * ((n + 1) ^ 25 + (Sq + 1) ^ 25) = 2 ^ 200 * (n + 1) ^ 25 + 2 ^ 200 * (Sq + 1) ^ 25 := by ring
  omega

/-- **`winCore` with the loop's `q`-part** (`hloop`'s second summand), at the merged `q`-slot. -/
theorem winCoreQ (sources : EightSources) (mask : MaskProducer) (MB : List Bool) (a : PointwisePCPPAlgorithm)
    (rq : PCPPRequest a.minimumArity)
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (bits : List Bool) (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (L target : Nat) (mode : Bool) (Rc b cwid cw D Vb Pw W Ld n Sq cL dL wCs wEs : Nat)
    (hread : SourceRequest.CoordBridge.CoordReads mode coordinate bits)
    (hbits : bits.length ≤ n) (h4S : 4 ≤ Sq)
    (hQ : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) ≤ Sq)
    (hJ : (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left)).monomials.length +
      (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right)).monomials.length + 1 ≤ Sq)
    (hcwidS : cwid ≤ Sq) (hcwS : cw ≤ Sq) (hDS : D ≤ Sq) (h4D : 4 ≤ D) (hLS : L ≤ Sq) (htS : target ≤ Sq) (hbS : b ≤ Sq)
    (hVbS : Vb ≤ Sq) (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hYb : ∀ m, m ≤ (monomials coordinate ph ci).length →
      WordsCost.Yb (decompositionOf sources) (requestAt coordinate ph ci L target mode m, MB) ≤ Sq)
    (hloop : ∀ m, m ≤ (monomials coordinate ph ci).length →
      loopW sources a rq ci coordinate ph L target Pw W Ld mode m ≤ cL * (n + 1) ^ dL + wCs * (Sq + 1) ^ wEs)
    (hE : Ebd n Sq cL dL (WordsCost.wC (decompositionOf sources) mask + wCs) (max (WordsCost.wE (decompositionOf sources) mask) wEs) ≤ Rc) :
    G7Win sources mask MB a rq coordinate bits ph ci L target mode Rc b cwid cw D (20 * Sq + 50) Vb Pw W Ld := by
  obtain ⟨har, hsys, haux, h2c, hcl⟩ := shapes_le a rq
  have wy : ∀ m, m ≤ (monomials coordinate ph ci).length → _ := fun m hm =>
    WordsCost.windows_of_Yb (decompositionOf sources) (requestAt coordinate ph ci L target mode m) MB Rc
      (w_words n Sq cL dL _ _ Rc hE _ MB _ (hYb m hm))
  refine
    { hc := SourceBudget.pair_cap a rq ci
      hwinA := w_litCost a rq ci n Sq cL dL _ _ Rc hE hQ h4S
      hQR := w_QR a rq n Sq cL dL _ _ Rc hE hQ
      hiL := w_idx a rq n Sq cL dL _ _ Rc hE hQ _
      hiR := w_idx a rq n Sq cL dL _ _ Rc hE hQ _
      hcL := w_count a rq n Sq cL dL _ _ Rc hE bits hbits hQ _
      hcR := w_count a rq n Sq cL dL _ _ Rc hE bits hbits hQ _
      hbig := w_big n Sq cL dL _ _ Rc hE _ _ hJ
      hwinR := ?_
      hHfit := fun m hm => w_fits n Sq cL dL _ _ Rc hE mode rq.arity L target _ D (by omega) hLS htS
        (FactorLoop.factorsAt_le coordinate ph ci m) h4S h4D hDS
      hbigR := w_coefBig n Sq cL dL _ _ Rc hE Vb _ b cw hVbS (by omega) hbS hcwS
      hNw := fun m hm => (wy m hm).1
      hS := fun m hm => (wy m hm).2.1
      hT := fun m hm => (wy m hm).2.2.1
      cq := fun m hm => (wy m hm).2.2.2.1
      ck := fun m hm => (wy m hm).2.2.2.2.1
      cm := fun m hm => (wy m hm).2.2.2.2.2.1
      ci' := fun m hm => (wy m hm).2.2.2.2.2.2.1
      hneed := fun m hm => w_need n Sq cL dL _ _ Rc hE _ MB _ (hYb m hm)
      cl1 := fun m hm => (wy m hm).2.2.2.2.2.2.2.1
      cl2 := (wy 0 (Nat.zero_le _)).2.2.2.2.2.2.2.2
      hwin := fun m hm => (winCostQ sources mask MB a rq ci coordinate bits ph L target cwid cw D b Vb Pw W Ld n Sq cL dL wCs wEs mode m
        hbits hQ hJ hcwidS hcwS hDS hLS htS hbS hVbS hcw1 hcoef hcoefV (hYb m hm) (hloop m hm)).trans hE
      hDR := by have := w_D n Sq cL dL _ _ Rc hE D hDS; omega
      hDC := w_D n Sq cL dL _ _ Rc hE D hDS
      hRc1 := w_one n Sq cL dL _ _ Rc hE }
  intro jj idx ts hjj hts hidx
  have key : ∀ l : Literal ((a.output rq).systematicBits + (a.output rq).auxiliaryBits),
      jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l).val →
      (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l)).monomials.length + 1 ≤ Sq →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc := by
    intro l hl hlen
    obtain ⟨ts', hts', hmap, -⟩ := hread (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l)
    rw [← hl, hts] at hts'
    have e : ts = ts' := Option.some.inj hts'
    subst e
    have hl2 := congrArg List.length hmap
    rw [List.length_map, List.length_map] at hl2
    have hi := idx_lt a rq Sq hQ l
    exact w_reader n Sq cL dL _ _ Rc hE bits jj idx cwid cw hbits (by omega) (by omega) hcwidS hcwS
  rcases hjj with h | h
  · exact key _ h (by omega)
  · exact key _ h (by omega)

section v5
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p

/-- **`g7OnsetQ`**: `g7Onset` at the merged `q`-slot (`wC + wCs`, `max wE wEs`). -/
def g7OnsetQ (L target tg cL dL wCs wEs : Nat) (hk : max 25 dL + 1 ≤ 𝔨 + 2) : Nat :=
  Classical.choose (onset_exists selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg 𝔨 cL dL
    (WordsCost.wC (decompositionOf sources) mask + wCs) (max (WordsCost.wE (decompositionOf sources) mask) wEs) hk)

theorem g7OnsetQ_spec (L target tg cL dL wCs wEs : Nat) (hk : max 25 dL + 1 ≤ 𝔨 + 2) (n : Nat)
    (hn : g7OnsetQ selector xtra mask packets rows sources gamma hg hh p L target tg cL dL wCs wEs hk ≤ n) :
    Ebd n (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n)) cL dL
        (WordsCost.wC (decompositionOf sources) mask + wCs) (max (WordsCost.wE (decompositionOf sources) mask) wEs) ≤
      RuntimeShape.tableClass L 0 (C10PartsSchedule.widthAt sources 𝔨 n) :=
  Classical.choose_spec (onset_exists selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg 𝔨 cL dL
    (WordsCost.wC (decompositionOf sources) mask + wCs) (max (WordsCost.wE (decompositionOf sources) mask) wEs) hk) n hn

end v5

end
end NearCubicWires.SourceRequest.SelWinLoop
end
