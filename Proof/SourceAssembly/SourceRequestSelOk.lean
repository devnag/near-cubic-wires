import Proof.SourceAssembly.SourceRequestSelSymMach

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CoordBridge
noncomputable section

section
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- **`hOk` from the coordinate circuits' admission**, any producer, any mode. -/
theorem ok_of_adm {mode : Bool} {da : RepairRepresentation.DecompositionAlgorithm}
    (P : FactorLoop.FactorProducer mode da pcpp)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hread : CoordReads mode coordinate bits) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (hnone : P.Ok none)
    (hsys : ∀ idx, P.Ok (some (RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic idx)))
    (hadm : ∀ j, ∀ mo ∈ (coordinate j).monomials, ∀ x ∈ mo.factors, P.Ok (some x))
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length) (i : Fin 4) :
    P.Ok (FactorLoop.factorsAt coordinate ph ci m)[i.val]? := by
  by_cases hlt : m < (FactorLoop.monomials coordinate ph ci).length
  · obtain ⟨σ₀, -, hmem, hfa⟩ := SourceFactorSel.SlotSpec.factorsAt_eq pcpp coordinate ph ci (Tof coordinate ci)
      (eOf pcpp ci) rfl rfl (fun h => atomAt_sys pcpp _ h) (fun h => atomAt_sys pcpp _ h) m hlt
    have hone : ∀ (r : Bool) (j : Nat) (h : j < (Tof coordinate ci r).length),
        ((Tof coordinate ci r)[j]).factors.length = 1 := by
      intro r j h
      cases r with
      | false =>
        obtain ⟨ts, -, hmap, -⟩ := hread (literalIndex (pcpp.clauses ci).left)
        exact SourceFactorSel.SlotRead.one_of_map coordinate _ ts hmap j h
      | true =>
        obtain ⟨ts, -, hmap, -⟩ := hread (literalIndex (pcpp.clauses ci).right)
        exact SourceFactorSel.SlotRead.one_of_map coordinate _ ts hmap j h
    have hok := SourceFactorSel.SlotSpec.siteSel_ok ph
      (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length σ₀ hmem
    have hfa' := hfa.trans (SourceFactorSel.SlotSpec.real_factors (Tof coordinate ci) (eOf pcpp ci) _ _ hone σ₀ hok)
    rw [hfa', List.getElem?_map]
    cases hf : σ₀.facs[i.val]? with
    | none => exact hnone
    | some f =>
      have hfok := hok f (List.mem_of_getElem? hf)
      cases f with
      | sys r =>
        cases r with
        | false =>
          have hs : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits := by
            simpa [SourceFactorSel.SlotSpec.FacOK] using hfok
          show P.Ok (some (atomAt pcpp (literalIndex (pcpp.clauses ci).left).val))
          rw [atomAt_sys pcpp _ hs]; exact hsys _
        | true =>
          have hs : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits := by
            simpa [SourceFactorSel.SlotSpec.FacOK] using hfok
          show P.Ok (some (atomAt pcpp (literalIndex (pcpp.clauses ci).right).val))
          rw [atomAt_sys pcpp _ hs]; exact hsys _
      | term r j =>
        cases r with
        | false =>
          have hj : j < (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length := by
            simpa [SourceFactorSel.SlotSpec.FacOK] using hfok
          obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hone false j hj)
          have hg : (Tof coordinate ci false)[j]? = some ((coordinate (literalIndex (pcpp.clauses ci).left)).monomials[j]) :=
            List.getElem?_eq_getElem hj
          show P.Ok (some ((((Tof coordinate ci false)[j]?).bind fun mo => mo.factors.head?).getD (eOf pcpp ci false)))
          have ha' : ((coordinate (literalIndex (pcpp.clauses ci).left)).monomials[j]).factors = [a] := ha
          rw [hg, Option.bind_some, ha']
          exact hadm _ _ (List.getElem_mem hj) a (by rw [ha']; exact List.mem_singleton_self a)
        | true =>
          have hj : j < (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length := by
            simpa [SourceFactorSel.SlotSpec.FacOK] using hfok
          obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hone true j hj)
          have hg : (Tof coordinate ci true)[j]? = some ((coordinate (literalIndex (pcpp.clauses ci).right)).monomials[j]) :=
            List.getElem?_eq_getElem hj
          show P.Ok (some ((((Tof coordinate ci true)[j]?).bind fun mo => mo.factors.head?).getD (eOf pcpp ci true)))
          have ha' : ((coordinate (literalIndex (pcpp.clauses ci).right)).monomials[j]).factors = [a] := ha
          rw [hg, Option.bind_some, ha']
          exact hadm _ _ (List.getElem_mem hj) a (by rw [ha']; exact List.mem_singleton_self a)
  · have heq : m = (FactorLoop.monomials coordinate ph ci).length := by omega
    rw [heq, FactorLoop.factorsAt_end]
    exact hnone

/-- **THR: `hOk` from the threshold circuits' caps.** -/
theorem ok_thr (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hread : CoordReads false coordinate bits) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (hcapT : ∀ j, ∀ mo ∈ (coordinate j).monomials, ∀ c,
      RepairSource.CloseoutFinal.C10TotalDecode.Atom.threshold c ∈ mo.factors →
      4 ≤ Ld ∧ c.descriptionBits ≤ Ld ∧ c.wireCount ≤ W ∧
        CloseoutRowsCircuitCapacity.capacity (ThrSwitch.codeWidth Ld) ≤ Pw)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length) (i : Fin 4) :
    (SelBack.PT (pcpp := pcpp) da Pw W Ld).Ok (FactorLoop.factorsAt coordinate ph ci m)[i.val]? := by
  refine ok_of_adm (SelBack.PT (pcpp := pcpp) da Pw W Ld) coordinate bits hread ph ci trivial (fun _ => trivial) ?_ m hm i
  intro j mo hmo x hx
  obtain ⟨ts, -, -, horig⟩ := hread j
  have hk := horig mo hmo x hx
  cases x with
  | systematic idx => exact trivial
  | symmetric c => simp [SourceFactorSel.Modes.kindOf] at hk
  | threshold c => exact hcapT j mo hmo c hx

/-- **SYM: `hOk` from the symmetric circuits' caps.** -/
theorem ok_sym (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hread : CoordReads true coordinate bits) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (hcapS : ∀ j, ∀ mo ∈ (coordinate j).monomials, ∀ c,
      RepairSource.CloseoutFinal.C10TotalDecode.Atom.symmetric c ∈ mo.factors →
      4 ≤ Ld ∧ c.descriptionBits ≤ Ld ∧ c.wireCount ≤ W ∧
        CloseoutRowsCircuitCapacity.capacity (SymOriginal.symCodeWidth Ld) ≤ Pw)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length) (i : Fin 4) :
    (SelBackSym.PS (pcpp := pcpp) da Pw W Ld).Ok (FactorLoop.factorsAt coordinate ph ci m)[i.val]? := by
  refine ok_of_adm (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) coordinate bits hread ph ci trivial (fun _ => trivial) ?_ m hm i
  intro j mo hmo x hx
  obtain ⟨ts, -, -, horig⟩ := hread j
  have hk := horig mo hmo x hx
  cases x with
  | systematic idx => exact trivial
  | threshold c => simp [SourceFactorSel.Modes.kindOf] at hk
  | symmetric c => exact hcapS j mo hmo c hx

/-- `need = 1` for both producers. -/
theorem need_thr (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld Rc : Nat) (hRc : 1 ≤ Rc)
    (o : Option (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)) :
    (SelBack.PT (pcpp := pcpp) da Pw W Ld).need o ≤ Rc := hRc

theorem need_sym (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld Rc : Nat) (hRc : 1 ≤ Rc)
    (o : Option (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)) :
    (SelBackSym.PS (pcpp := pcpp) da Pw W Ld).need o ≤ Rc := hRc

end

end
end NearCubicWires.SourceRequest.SelLocal

