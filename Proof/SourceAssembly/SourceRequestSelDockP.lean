import Proof.SourceAssembly.SourceRequestSelLocalP
import Proof.SourceAssembly.SourceRequestSelDockK

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.SourceConstruction
noncomputable section

section S
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
  (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tT da) ≤ gW)

theorem local_of_restIn4P (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits)) (bits : List Bool) (Pw W Ld L target cwid cw D b Rc m QK : Nat) (pw : List Bool)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hKc : ∀ j, K (cacheT j) ∧ K0 (cacheT j) = PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
      (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j ∧ KH0 (cacheT j) = 0)
    (hKw : ∀ x : Fin V, x.val = 1 → K x ∧ K0 x = RepairOrdinary.frame bits ∧ KH0 x = 0)
    (hKr : ∀ i, i < 10 → ∀ x : Fin V, x.val = d.B + 29 + restPc eX pX gW + i →
      K x ∧ K0 x = ZeroPadding.pad Rc (resW r.arity Pw W Ld L target cwid cw i) ∧ KH0 x = 0)
    (hKD : ∀ x : Fin V, x.val = d.B + 41 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate D true) ∧ KH0 x = 0)
    (hKt : K terminal ∧ K0 terminal = ZeroPadding.pad QK (List.replicate (2 ^ (a.output r).clauseBits) true) ∧
      KH0 terminal = 0)
    (hKb : ∀ x : Fin V, x.val = d.B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate b true) ∧ KH0 x = 0)
    (H : Fin V → Nat) (A : Fin V → List Bool)
    (hin : Rest.RestIn4 d eX pX gW Rc (Dims.pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0 m H A) :
    (∀ z, H (gS e hV da cacheT terminal hres hN z) = 0) ∧
    LocalInK (tT da) false (fun z => A (gS e hV da cacheT terminal hres hN z))
      (fun j => PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
        (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j)
      bits m r.arity Pw W Ld L target cwid cw D (2 ^ (a.output r).clauseBits) b Rc QK := by
  obtain ⟨⟨hout, hcur, hcurH, hK⟩, -⟩ := hin
  have eP : restPc eX pX gW = 71 + (eX + pX) + gW := by unfold restPc; omega
  -- the value of a high local port
  have hval : ∀ z : Fin (NF + (19 + 4 * tT da)), ¬ Low z.val →
      (gS e hV da cacheT terminal hres hN z).val = d.B + hv (restPc eX pX gW) (eX + pX) z.val :=
    fun z hz => gS_high e hV da cacheT terminal hres hN z hz
  have ecur : gS e hV da cacheT terminal hres hN (up 20) = Dims.pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩ :=
    Fin.ext (by rw [hval _ (by unfold Low; show ¬ (20 < 19 ∨ 20 = 19 ∨ 20 = 32); decide), up_val]; show d.B + hv _ _ 20 = d.B + 19 + 64; rw [hv_20])
  have hres21 : ∀ i (hi : i < 10), (gS e hV da cacheT terminal hres hN (up ⟨21 + i, by unfold NF; omega⟩)).val =
      d.B + 29 + restPc eX pX gW + i := by
    intro i hi
    rw [hval _ (by unfold Low; show ¬ (21 + i < 19 ∨ 21 + i = 19 ∨ 21 + i = 32); omega), up_val]
    show d.B + hv _ _ (21 + i) = _
    rw [hv_21 _ _ _ hi]; omega
  have hres31 : (gS e hV da cacheT terminal hres hN (up 31)).val = d.B + 41 + restPc eX pX gW := by
    rw [hval _ (by unfold Low; show ¬ (31 < 19 ∨ 31 = 19 ∨ 31 = 32); decide), up_val]; show d.B + hv _ _ 31 = _; rw [hv_31]; omega
  have hres39 : (gS e hV da cacheT terminal hres hN (up 39)).val = d.B + 48 + restPc eX pX gW := by
    rw [hval _ (by unfold Low; show ¬ (39 < 19 ∨ 39 = 19 ∨ 39 = 32); decide), up_val]; show d.B + hv _ _ 39 = _; rw [hv_39]; omega
  have kw := hKw _ (gS_wit e hV da cacheT terminal hres hN)
  have kr : ∀ i (hi : i < 10), K (gS e hV da cacheT terminal hres hN (up ⟨21 + i, by unfold NF; omega⟩)) ∧
      K0 (gS e hV da cacheT terminal hres hN (up ⟨21 + i, by unfold NF; omega⟩)) =
        ZeroPadding.pad Rc (resW r.arity Pw W Ld L target cwid cw i) ∧
      KH0 (gS e hV da cacheT terminal hres hN (up ⟨21 + i, by unfold NF; omega⟩)) = 0 :=
    fun i hi => hKr i hi _ (hres21 i hi)
  have kD := hKD _ hres31
  have kb := hKb _ hres39
  have hlow : ∀ z : Fin (NF + (19 + 4 * tT da)), Low z.val → H (gS e hV da cacheT terminal hres hN z) = 0 := by
    intro z hz
    unfold Low at hz
    by_cases h19 : z.val < 19
    · have ez : z = up ⟨z.val, by unfold NF; omega⟩ := Fin.ext rfl
      rw [ez, gS_cache e hV da cacheT terminal hres hN ⟨z.val, h19⟩]
      exact (hK _ (hKc _).1).2.trans (hKc _).2.2
    by_cases e19 : z.val = 19
    · have ez : z = up 19 := Fin.ext (by rw [up_val]; exact e19)
      rw [ez]; exact (hK _ kw.1).2.trans kw.2.2
    · have ez : z = up 32 := Fin.ext (by rw [up_val]; show z.val = 32; omega)
      rw [ez, gS_term e hV da cacheT terminal hres hN]
      exact (hK _ hKt.1).2.trans hKt.2.2
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro z
    by_cases hz : Low z.val
    · exact hlow z hz
    unfold Low at hz
    by_cases e20 : z.val = 20
    · have ez : z = up 20 := Fin.ext (by rw [up_val]; exact e20)
      rw [ez, ecur]; exact hcurH
    by_cases h31 : z.val < 31
    · have ez : z = up ⟨21 + (z.val - 21), by unfold NF; omega⟩ := Fin.ext (by rw [up_val]; show z.val = 21 + (z.val - 21); omega)
      have k := kr (z.val - 21) (by omega)
      rw [ez]; exact (hK _ k.1).2.trans k.2.2
    by_cases e31 : z.val = 31
    · have ez : z = up 31 := Fin.ext (by rw [up_val]; exact e31)
      rw [ez]; exact (hK _ kD.1).2.trans kD.2.2
    by_cases e39 : z.val = 39
    · have ez : z = up 39 := Fin.ext (by rw [up_val]; exact e39)
      rw [ez]; exact (hK _ kb.1).2.trans kb.2.2
    · exact (hout _ (gS_out e hV da cacheT terminal hres hN z (by omega) e39)).2
  · intro j
    rw [gS_cache e hV da cacheT terminal hres hN j]
    exact (hK _ (hKc j).1).1.trans (hKc j).2.1
  · exact (hK _ kw.1).1.trans kw.2.1
  · show A (gS e hV da cacheT terminal hres hN (up 20)) = _
    rw [ecur]; exact hcur
  · have k := kr 0 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · have k := kr 1 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · have k := kr 2 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · have k := kr 3 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · intro i
    have k := kr (4 + i.val) (by omega)
    have e4 : resW r.arity Pw W Ld L target cwid cw (4 + i.val) =
        RepairOrdinary.frame (SourceFactorSel.Header.fields false r.arity L target 0 ⟨i.val, by omega⟩) := by
      have h0 : 4 + i.val ≠ 0 := by omega
      have h1 : 4 + i.val ≠ 1 := by omega
      have h2 : 4 + i.val ≠ 2 := by omega
      have h3 : 4 + i.val ≠ 3 := by omega
      have h8 : 4 + i.val < 8 := by omega
      simp only [resW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, dif_pos h8]
      congr 3
      omega
    have ei : (up ⟨25 + i.val, by have := i.isLt; unfold NF; omega⟩ : Fin (NF + (19 + 4 * tT da))) =
        up ⟨21 + (4 + i.val), by have := i.isLt; unfold NF; omega⟩ := Fin.ext (by rw [up_val, up_val]; show 25 + i.val = 21 + (4 + i.val); omega)
    show A (gS e hV da cacheT terminal hres hN (up ⟨25 + i.val, _⟩)) = _
    rw [ei, (hK _ k.1).1, k.2.1, e4]
  · have k := kr 8 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · have k := kr 9 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · exact (hK _ kD.1).1.trans kD.2.1
  · show A (gS e hV da cacheT terminal hres hN (up 32)) = _
    rw [gS_term e hV da cacheT terminal hres hN]
    exact (hK _ hKt.1).1.trans hKt.2.1
  · exact (hK _ kb.1).1.trans kb.2.1
  · intro k hk h33 h39
    exact (hout _ (gS_out e hV da cacheT terminal hres hN _ h33 h39)).1
  · intro x
    exact (hout _ (gS_out e hV da cacheT terminal hres hN _ (by rw [Fin.val_natAdd]; unfold NF; omega)
      (by rw [Fin.val_natAdd]; unfold NF; omega))).1

theorem selRun_SP (Pw W Ld : Nat)
    (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (hread : CoordReads false coordinate bits) (ph : Phase)
    (L target cwid cw D b Rc c qCap QK : Nat) (pw : List Bool)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hKc : ∀ j, K (cacheT j) ∧ K0 (cacheT j) = PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
      (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j ∧ KH0 (cacheT j) = 0)
    (hKw : ∀ x : Fin V, x.val = 1 → K x ∧ K0 x = RepairOrdinary.frame bits ∧ KH0 x = 0)
    (hKr : ∀ i, i < 10 → ∀ x : Fin V, x.val = d.B + 29 + restPc eX pX gW + i →
      K x ∧ K0 x = ZeroPadding.pad Rc (resW r.arity Pw W Ld L target cwid cw i) ∧ KH0 x = 0)
    (hKD : ∀ x : Fin V, x.val = d.B + 41 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate D true) ∧ KH0 x = 0)
    (hKt : K terminal ∧ K0 terminal = ZeroPadding.pad QK (List.replicate (2 ^ (a.output r).clauseBits) true) ∧
      KH0 terminal = 0)
    (hKb : ∀ x : Fin V, x.val = d.B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate b true) ∧ KH0 x = 0)
    (hci : Function.Injective cacheT) (hcF : ∀ j, (cacheT j).val < d.F) (htF : terminal.val < d.F)
    (hc1 : ∀ j, (cacheT j).val ≠ 1) (hct : ∀ j, cacheT j ≠ terminal) (ht1 : terminal.val ≠ 1)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
    (hwinA : litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 1 ≤ Rc)
    (hiL : index ((a.output r).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output r).clauses ci).right + 3 ≤ Rc)
    (hcL : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length ≤ Rc)
    (hcwid : cwid = ThrSwitch.codeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex ((a.output r).clauses ci).left).val ∨
      jj = (literalIndex ((a.output r).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : r.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : ∀ m, m ≤ (FactorLoop.monomials coordinate ph ci).length →
      SourceFactorSel.HdrBlock.Fits false r.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (Vb : Nat) (hV4 : 4 ≤ Vb)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hbigR : SourceFactorSel.CoefR.coefBigR Vb (2 ^ (a.output r).clauseBits) b (cw + rhoW) ≤ Rc) :
    SourceFactorSel.Item4.SelRun (RecoveryFocus.machine (gS e hV da cacheT terminal hres hN) (selThrM ph da))
      (fun m => selThrCost a r ci coordinate bits ph L target cwid cw D b m)
      (PT (pcpp := a.output r) da Pw W Ld) coordinate ph ci L target Rc b qCap
      (fun x => gS e hV da cacheT terminal hres hN (rgP (PT (pcpp := a.output r) da Pw W Ld) x))
      (Dims.queryCopy e.ext2.ext1.ext hV)
      (Dims.pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => Dims.pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩)
      (fun x => ∃ z : Fin NF, 100 ≤ z.val ∧ gS e hV da cacheT terminal hres hN (up z) = x)
      (Rest.RestIn4 d eX pX gW Rc (Dims.pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0) :=
  selRun_thrP da Pw W Ld a r ci coordinate bits hread ph L target cwid cw D b Rc c qCap QK pw
    (gS e hV da cacheT terminal hres hN) (gS_inj e hV da cacheT terminal hres hN hci hcF htF hc1 hct ht1)
    (Dims.queryCopy e.ext2.ext1.ext hV) _ _ (gS_nT e hV da cacheT terminal hres hN)
    (gS_coefT e hV da cacheT terminal hres hN) _
    (fun m H A hin => local_of_restIn4P e hV da cacheT terminal hres hN a r ci bits Pw W Ld L target cwid cw D b Rc m QK pw
      K K0 KH0 hKc hKw hKr hKD hKt hKb H A hin)
    hc hwinA hQR hiL hiR hcL hcR hbig hcwid h2cw hwinR hqD hPD hWD hLD hDR hDC hHfit hcw1 hcoef Vb hV4 hcoefV hbigR

end S

section SS
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
  (da : RepairRepresentation.DecompositionAlgorithm) (cacheT : Fin 19 → Fin V) (terminal : Fin V)
  (hres : 49 + restPc eX pX gW ≤ d.res) (hN : NF + (19 + 4 * tS) ≤ gW)

theorem local_of_restIn4SP (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits)) (bits : List Bool) (Pw W Ld L target cwid cw D b Rc m QK : Nat) (pw : List Bool)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hKc : ∀ j, K (cacheT j) ∧ K0 (cacheT j) = PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
      (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j ∧ KH0 (cacheT j) = 0)
    (hKw : ∀ x : Fin V, x.val = 1 → K x ∧ K0 x = RepairOrdinary.frame bits ∧ KH0 x = 0)
    (hKr : ∀ i, i < 10 → ∀ x : Fin V, x.val = d.B + 29 + restPc eX pX gW + i →
      K x ∧ K0 x = ZeroPadding.pad Rc (resWS r.arity Pw W Ld L target cwid cw i) ∧ KH0 x = 0)
    (hKD : ∀ x : Fin V, x.val = d.B + 41 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate D true) ∧ KH0 x = 0)
    (hKt : K terminal ∧ K0 terminal = ZeroPadding.pad QK (List.replicate (2 ^ (a.output r).clauseBits) true) ∧
      KH0 terminal = 0)
    (hKb : ∀ x : Fin V, x.val = d.B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate b true) ∧ KH0 x = 0)
    (H : Fin V → Nat) (A : Fin V → List Bool)
    (hin : Rest.RestIn4 d eX pX gW Rc (Dims.pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0 m H A) :
    (∀ z, H (gSS e hV da cacheT terminal hres hN z) = 0) ∧
    LocalInK tS true (fun z => A (gSS e hV da cacheT terminal hres hN z))
      (fun j => PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
        (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j)
      bits m r.arity Pw W Ld L target cwid cw D (2 ^ (a.output r).clauseBits) b Rc QK := by
  obtain ⟨⟨hout, hcur, hcurH, hK⟩, -⟩ := hin
  have eP : restPc eX pX gW = 71 + (eX + pX) + gW := by unfold restPc; omega
  -- the value of a high local port
  have hval : ∀ z : Fin (NF + (19 + 4 * tS)), ¬ Low z.val →
      (gSS e hV da cacheT terminal hres hN z).val = d.B + hv (restPc eX pX gW) (eX + pX) z.val :=
    fun z hz => gSS_high e hV da cacheT terminal hres hN z hz
  have ecur : gSS e hV da cacheT terminal hres hN (up 20) = Dims.pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩ :=
    Fin.ext (by rw [hval _ (by unfold Low; show ¬ (20 < 19 ∨ 20 = 19 ∨ 20 = 32); decide), up_val]; show d.B + hv _ _ 20 = d.B + 19 + 64; rw [hv_20])
  have hres21 : ∀ i (hi : i < 10), (gSS e hV da cacheT terminal hres hN (up ⟨21 + i, by unfold NF; omega⟩)).val =
      d.B + 29 + restPc eX pX gW + i := by
    intro i hi
    rw [hval _ (by unfold Low; show ¬ (21 + i < 19 ∨ 21 + i = 19 ∨ 21 + i = 32); omega), up_val]
    show d.B + hv _ _ (21 + i) = _
    rw [hv_21 _ _ _ hi]; omega
  have hres31 : (gSS e hV da cacheT terminal hres hN (up 31)).val = d.B + 41 + restPc eX pX gW := by
    rw [hval _ (by unfold Low; show ¬ (31 < 19 ∨ 31 = 19 ∨ 31 = 32); decide), up_val]; show d.B + hv _ _ 31 = _; rw [hv_31]; omega
  have hres39 : (gSS e hV da cacheT terminal hres hN (up 39)).val = d.B + 48 + restPc eX pX gW := by
    rw [hval _ (by unfold Low; show ¬ (39 < 19 ∨ 39 = 19 ∨ 39 = 32); decide), up_val]; show d.B + hv _ _ 39 = _; rw [hv_39]; omega
  have kw := hKw _ (gSS_wit e hV da cacheT terminal hres hN)
  have kr : ∀ i (hi : i < 10), K (gSS e hV da cacheT terminal hres hN (up ⟨21 + i, by unfold NF; omega⟩)) ∧
      K0 (gSS e hV da cacheT terminal hres hN (up ⟨21 + i, by unfold NF; omega⟩)) =
        ZeroPadding.pad Rc (resWS r.arity Pw W Ld L target cwid cw i) ∧
      KH0 (gSS e hV da cacheT terminal hres hN (up ⟨21 + i, by unfold NF; omega⟩)) = 0 :=
    fun i hi => hKr i hi _ (hres21 i hi)
  have kD := hKD _ hres31
  have kb := hKb _ hres39
  have hlow : ∀ z : Fin (NF + (19 + 4 * tS)), Low z.val → H (gSS e hV da cacheT terminal hres hN z) = 0 := by
    intro z hz
    unfold Low at hz
    by_cases h19 : z.val < 19
    · have ez : z = up ⟨z.val, by unfold NF; omega⟩ := Fin.ext rfl
      rw [ez, gSS_cache e hV da cacheT terminal hres hN ⟨z.val, h19⟩]
      exact (hK _ (hKc _).1).2.trans (hKc _).2.2
    by_cases e19 : z.val = 19
    · have ez : z = up 19 := Fin.ext (by rw [up_val]; exact e19)
      rw [ez]; exact (hK _ kw.1).2.trans kw.2.2
    · have ez : z = up 32 := Fin.ext (by rw [up_val]; show z.val = 32; omega)
      rw [ez, gSS_term e hV da cacheT terminal hres hN]
      exact (hK _ hKt.1).2.trans hKt.2.2
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro z
    by_cases hz : Low z.val
    · exact hlow z hz
    unfold Low at hz
    by_cases e20 : z.val = 20
    · have ez : z = up 20 := Fin.ext (by rw [up_val]; exact e20)
      rw [ez, ecur]; exact hcurH
    by_cases h31 : z.val < 31
    · have ez : z = up ⟨21 + (z.val - 21), by unfold NF; omega⟩ := Fin.ext (by rw [up_val]; show z.val = 21 + (z.val - 21); omega)
      have k := kr (z.val - 21) (by omega)
      rw [ez]; exact (hK _ k.1).2.trans k.2.2
    by_cases e31 : z.val = 31
    · have ez : z = up 31 := Fin.ext (by rw [up_val]; exact e31)
      rw [ez]; exact (hK _ kD.1).2.trans kD.2.2
    by_cases e39 : z.val = 39
    · have ez : z = up 39 := Fin.ext (by rw [up_val]; exact e39)
      rw [ez]; exact (hK _ kb.1).2.trans kb.2.2
    · exact (hout _ (gSS_out e hV da cacheT terminal hres hN z (by omega) e39)).2
  · intro j
    rw [gSS_cache e hV da cacheT terminal hres hN j]
    exact (hK _ (hKc j).1).1.trans (hKc j).2.1
  · exact (hK _ kw.1).1.trans kw.2.1
  · show A (gSS e hV da cacheT terminal hres hN (up 20)) = _
    rw [ecur]; exact hcur
  · have k := kr 0 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · have k := kr 1 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · have k := kr 2 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · have k := kr 3 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · intro i
    have k := kr (4 + i.val) (by omega)
    have e4 : resWS r.arity Pw W Ld L target cwid cw (4 + i.val) =
        RepairOrdinary.frame (SourceFactorSel.Header.fields true r.arity L target 0 ⟨i.val, by omega⟩) := by
      have h0 : 4 + i.val ≠ 0 := by omega
      have h1 : 4 + i.val ≠ 1 := by omega
      have h2 : 4 + i.val ≠ 2 := by omega
      have h3 : 4 + i.val ≠ 3 := by omega
      have h8 : 4 + i.val < 8 := by omega
      simp only [resWS, if_neg h0, if_neg h1, if_neg h2, if_neg h3, dif_pos h8]
      congr 3
      omega
    have ei : (up ⟨25 + i.val, by have := i.isLt; unfold NF; omega⟩ : Fin (NF + (19 + 4 * tS))) =
        up ⟨21 + (4 + i.val), by have := i.isLt; unfold NF; omega⟩ := Fin.ext (by rw [up_val, up_val]; show 25 + i.val = 21 + (4 + i.val); omega)
    show A (gSS e hV da cacheT terminal hres hN (up ⟨25 + i.val, _⟩)) = _
    rw [ei, (hK _ k.1).1, k.2.1, e4]
  · have k := kr 8 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · have k := kr 9 (by decide)
    exact (hK _ k.1).1.trans k.2.1
  · exact (hK _ kD.1).1.trans kD.2.1
  · show A (gSS e hV da cacheT terminal hres hN (up 32)) = _
    rw [gSS_term e hV da cacheT terminal hres hN]
    exact (hK _ hKt.1).1.trans hKt.2.1
  · exact (hK _ kb.1).1.trans kb.2.1
  · intro k hk h33 h39
    exact (hout _ (gSS_out e hV da cacheT terminal hres hN _ h33 h39)).1
  · intro x
    exact (hout _ (gSS_out e hV da cacheT terminal hres hN _ (by rw [Fin.val_natAdd]; unfold NF; omega)
      (by rw [Fin.val_natAdd]; unfold NF; omega))).1

theorem selRun_S_symP (Pw W Ld : Nat)
    (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (hread : CoordReads true coordinate bits) (ph : Phase)
    (L target cwid cw D b Rc c qCap QK : Nat) (pw : List Bool)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hKc : ∀ j, K (cacheT j) ∧ K0 (cacheT j) = PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
      (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j ∧ KH0 (cacheT j) = 0)
    (hKw : ∀ x : Fin V, x.val = 1 → K x ∧ K0 x = RepairOrdinary.frame bits ∧ KH0 x = 0)
    (hKr : ∀ i, i < 10 → ∀ x : Fin V, x.val = d.B + 29 + restPc eX pX gW + i →
      K x ∧ K0 x = ZeroPadding.pad Rc (resWS r.arity Pw W Ld L target cwid cw i) ∧ KH0 x = 0)
    (hKD : ∀ x : Fin V, x.val = d.B + 41 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate D true) ∧ KH0 x = 0)
    (hKt : K terminal ∧ K0 terminal = ZeroPadding.pad QK (List.replicate (2 ^ (a.output r).clauseBits) true) ∧
      KH0 terminal = 0)
    (hKb : ∀ x : Fin V, x.val = d.B + 48 + restPc eX pX gW →
      K x ∧ K0 x = ZeroPadding.pad Rc (List.replicate b true) ∧ KH0 x = 0)
    (hci : Function.Injective cacheT) (hcF : ∀ j, (cacheT j).val < d.F) (htF : terminal.val < d.F)
    (hc1 : ∀ j, (cacheT j).val ≠ 1) (hct : ∀ j, cacheT j ≠ terminal) (ht1 : terminal.val ≠ 1)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
    (hwinA : litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 1 ≤ Rc)
    (hiL : index ((a.output r).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output r).clauses ci).right + 3 ≤ Rc)
    (hcL : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length ≤ Rc)
    (hcwid : cwid = SymOriginal.symCodeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex ((a.output r).clauses ci).left).val ∨
      jj = (literalIndex ((a.output r).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : r.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : ∀ m, m ≤ (FactorLoop.monomials coordinate ph ci).length →
      SourceFactorSel.HdrBlock.Fits true r.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (Vb : Nat) (hV4 : 4 ≤ Vb)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hbigR : SourceFactorSel.CoefR.coefBigR Vb (2 ^ (a.output r).clauseBits) b (cw + rhoW) ≤ Rc) :
    SourceFactorSel.Item4.SelRun (RecoveryFocus.machine (gSS e hV da cacheT terminal hres hN) (selSymM ph))
      (fun m => selSymCost a r ci coordinate bits ph L target cwid cw D b m)
      (SelBackSym.PS (pcpp := a.output r) da Pw W Ld) coordinate ph ci L target Rc b qCap
      (fun x => gSS e hV da cacheT terminal hres hN (rgP (SelBackSym.PS (pcpp := a.output r) da Pw W Ld) x))
      (Dims.queryCopy e.ext2.ext1.ext hV)
      (Dims.pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => Dims.pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩)
      (fun x => ∃ z : Fin NF, 100 ≤ z.val ∧ gSS e hV da cacheT terminal hres hN (up z) = x)
      (Rest.RestIn4 d eX pX gW Rc (Dims.pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0) :=
  selRun_symP da Pw W Ld a r ci coordinate bits hread ph L target cwid cw D b Rc c qCap QK pw
    (gSS e hV da cacheT terminal hres hN) (gSS_inj e hV da cacheT terminal hres hN hci hcF htF hc1 hct ht1)
    (Dims.queryCopy e.ext2.ext1.ext hV) _ _ (gSS_nT e hV da cacheT terminal hres hN)
    (gSS_coefT e hV da cacheT terminal hres hN) _
    (fun m H A hin => local_of_restIn4SP e hV da cacheT terminal hres hN a r ci bits Pw W Ld L target cwid cw D b Rc m QK pw
      K K0 KH0 hKc hKw hKr hKD hKt hKb H A hin)
    hc hwinA hQR hiL hiR hcL hcR hbig hcwid h2cw hwinR hqD hPD hWD hLD hDR hDC hHfit hcw1 hcoef Vb hV4 hcoefV hbigR

end SS

end
end NearCubicWires.SourceRequest.SelLocal

