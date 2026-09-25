import Proof.SourceAssembly.SourceRequestSelBackThrRun

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelBackSym
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

section slots
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- **The four slot pipelines' premises at call `m`** (SYM), from `CoordReads` and site_pairs' `T/e`. -/
theorem slot_hyps_sym (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hread : CoordReads true coordinate bits) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (e : Bool → RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length) (Ld cwid cw D Rc : Nat)
    (hcwid : cwid = SymOriginal.symCodeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (bmL bmR : List Bool)
    (hbmL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      bmL = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      bmR = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmD : bmL.length ≤ D ∧ bmR.length ≤ D)
    (hwin : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex (pcpp.clauses ci).left).val ∨
      jj = (literalIndex (pcpp.clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc) (i : Fin 4) (σ : Option Sel)
    (hσ : σ = selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m) :
    kindOf true ((FactorLoop.factorsAt coordinate ph ci m)[i.val]?) =
      (if fSys (facAt σ i.val) then .sys else if fTerm (facAt σ i.val) then .orig else .absent) ∧
    ¬ (fSys (facAt σ i.val) = true ∧ fTerm (facAt σ i.val) = true) ∧
    (fSys (facAt σ i.val) = true → bmOf ((FactorLoop.factorsAt coordinate ph ci m)[i.val]?) =
      (if fSide (facAt σ i.val) then bmR else bmL) ∧ (bmOf ((FactorLoop.factorsAt coordinate ph ci m)[i.val]?)).length ≤ D) ∧
    (fTerm (facAt σ i.val) = true →
      SourceFactorSel.Slot.TermOK bits (bitsOf true Ld ((FactorLoop.factorsAt coordinate ph ci m)[i.val]?))
        (if fSide (facAt σ i.val) then (literalIndex (pcpp.clauses ci).right).val
          else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ i.val)) cwid cw D Rc Rc) ∧
    (fTerm (facAt σ i.val) = true → ∀ ts, rawTerms bits (if fSide (facAt σ i.val) then (literalIndex (pcpp.clauses ci).right).val
          else (literalIndex (pcpp.clauses ci).left).val) = some ts → ∀ hi : fIdx (facAt σ i.val) < ts.length,
      SourceFactorSel.CoefBridge.tco T (facAt σ i.val) = (ts[fIdx (facAt σ i.val)]'hi).1) := by
  by_cases hlt : m < (FactorLoop.monomials coordinate ph ci).length
  · have hlt' := hlt
    rw [MonomialSpec.monomials_len] at hlt'
    obtain ⟨σ₀, hσ₀⟩ := selAt_some _ _ _ _ _ _ _ m hlt'
    obtain ⟨hk, hst, hsys, hterm⟩ := SourceFactorSel.SlotRead.slot_reads true pcpp coordinate bits hread ph ci T e
      hTL hTR heL heR m hlt σ₀ hσ₀ i.val
    have eσ : σ = some σ₀ := hσ.trans hσ₀
    subst eσ
    refine ⟨hk, hst, ?_, ?_, ?_⟩
    · intro hs
      obtain ⟨h, ho⟩ := hsys hs
      rw [ho]
      by_cases hr : fSide (facAt (some σ₀) i.val) = true
      · have ee : (if fSide (facAt (some σ₀) i.val) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) = (literalIndex (pcpp.clauses ci).right).val := if_pos hr
        have h' : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits := ee ▸ h
        have eF : (⟨_, h⟩ : Fin pcpp.systematicBits) = ⟨_, h'⟩ := Fin.ext ee
        rw [eF, if_pos hr]
        show PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h'⟩) = bmR ∧
          (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h'⟩)).length ≤ D
        rw [← hbmR h']; exact ⟨rfl, hbmD.2⟩
      · have ee : (if fSide (facAt (some σ₀) i.val) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) = (literalIndex (pcpp.clauses ci).left).val := if_neg hr
        have h' : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits := ee ▸ h
        have eF : (⟨_, h⟩ : Fin pcpp.systematicBits) = ⟨_, h'⟩ := Fin.ext ee
        rw [eF, if_neg hr]
        show PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h'⟩) = bmL ∧
          (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h'⟩)).length ≤ D
        rw [← hbmL h']; exact ⟨rfl, hbmD.1⟩
    · intro ht
      obtain ⟨x, ts, hi, ho, hko, hraw, hcode, -⟩ := hterm ht
      rw [ho]
      refine SourceFactorSel.Slot.termOK_of bits _ _ _ cwid cw D Rc Rc ts hi hraw ?_ h2cw
        (hwin _ _ ts (by split <;> simp) hraw hi) le_rfl
      rw [SourceFactorSel.SlotRead.bits_sym Ld x hko, hcwid, hcode]
    · intro ht ts hraw hi
      obtain ⟨x, ts', hi', ho, hko, hraw', hcode, htco⟩ := hterm ht
      have : ts' = ts := Option.some.inj (hraw'.symm.trans hraw)
      subst this
      exact htco
  · have heq : m = (FactorLoop.monomials coordinate ph ci).length := by omega
    have hlen := SourceFactorSel.KBridge.factorsAt_len true pcpp coordinate bits hread ph ci T e hTL hTR heL heR m hm
    have h0 : (FactorLoop.factorsAt coordinate ph ci m).length = 0 := by
      rw [heq, FactorLoop.factorsAt_end]; rfl
    have hk0 : kOf σ = 0 := by rw [hσ, ← hlen]; exact h0
    have hf := facAt_none_of_k σ hk0 i.val
    have ho : (FactorLoop.factorsAt coordinate ph ci m)[i.val]? = none := by
      rw [heq, FactorLoop.factorsAt_end]; rfl
    rw [ho, hf]
    refine ⟨rfl, by simp [fSys], by simp [fSys], by simp [fTerm], by simp [fTerm]⟩

end slots

section four
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- The SYM producer at the admission caps. -/
abbrev PS (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat) := SymSwitch.producer (pcpp := pcpp) da Pw W Ld

theorem slB_curvS (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat) (ph : Phase) (i : Fin 4)
    (j : Fin 1121) (hj : j.val < 4) (c : Fin 128) (hc : c.val = 6 + 4 * i.val + j.val) :
    slB (PS (pcpp := pcpp) da Pw W Ld) rfl i j = up (SelFront.curSl ph c) := by
  apply Fin.ext
  rw [slB_lo _ rfl i _ (by omega), up_val, SelFront.curSl_val]
  have := i.isLt
  simp only [loVal, show j.val < 17 by omega, if_true, inPort, show j.val < 4 from hj, hc,
    show ¬ (6 + 4 * i.val + j.val = 0) by omega, show ¬ (6 + 4 * i.val + j.val = 1) by omega,
    show ¬ (6 + 4 * i.val + j.val = 2) by omega, show ¬ (6 + 4 * i.val + j.val = 3) by omega,
    show ¬ (6 + 4 * i.val + j.val = 4) by omega, show ¬ (6 + 4 * i.val + j.val = 5) by omega, if_false]
  omega

theorem slB_inS (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat) (i : Fin 4) (k : Nat) (hk : 4 ≤ k) (hk' : k < 17) :
    slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨k, by omega⟩ =
      up ⟨inPort i.val k, by have := inPort_lt i.val i.isLt k hk'; unfold NF; omega⟩ := by
  apply Fin.ext
  rw [slB_lo _ rfl i _ (by simp; omega), up_val]
  simp [loVal, show k < 17 from hk']

end four

section keptS
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- A fixed port below `1400` or at/above `6000` is untouched by the four slots' private ports. -/
theorem kept_loS (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld k : Nat) (hk : k < 1400 ∨ (6000 ≤ k ∧ k < NF)) :
    SourceFactorSel.Slots4.Kept (slB (PS (pcpp := pcpp) da Pw W Ld) rfl)
      (up ⟨k, by rcases hk with hk | hk <;> unfold NF at * <;> omega⟩) := by
  intro i j e
  by_contra hj
  have hv := congrArg Fin.val e
  rw [up_val] at hv
  have := i.isLt; have := j.isLt
  by_cases hr : j.val < 33
  · rw [slB_rg _ rfl i j (by omega) hr, rg_val] at hv; unfold NF at *; omega
  · rw [slB_lo _ rfl i j (by omega)] at hv
    rcases loVal_cases i.val j.val i.isLt (by omega) with ⟨h1, e1, -⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1] at hv <;>
      simp only at hv <;> omega

/-- A region port other than the four slots' descriptor ports is untouched by them. -/
theorem kept_rgS (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (x : Fin (19 + 4 * (PS (pcpp := pcpp) da Pw W Ld).t))
    (hx : ∀ i n, FactorLoop.cslot (PS (pcpp := pcpp) da Pw W Ld) i ((PS (pcpp := pcpp) da Pw W Ld).descSlots n) ≠ x) :
    SourceFactorSel.Slots4.Kept (slB (PS (pcpp := pcpp) da Pw W Ld) rfl) (rgP _ x) := by
  intro i j e
  by_contra hj
  have := i.isLt; have := j.isLt
  by_cases hr : j.val < 33
  · rw [slB_rg _ rfl i j (by omega) hr] at e
    exact hx i _ (rgP_inj _ _ _ e)
  · have hv := congrArg Fin.val e
    rw [slB_lo _ rfl i j (by omega), rg_val] at hv
    unfold NF at hv
    rcases loVal_cases i.val j.val i.isLt (by omega) with ⟨h1, e1, -⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1] at hv <;> omega

end keptS

end
end NearCubicWires.SourceRequest.SelBackSym

