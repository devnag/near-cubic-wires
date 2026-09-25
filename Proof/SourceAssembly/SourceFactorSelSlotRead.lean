import Proof.SourceAssembly.SourceFactorSelSlot
import Proof.SourceAssembly.SourceFactorSelSlotSpec
import Proof.SourceAssembly.SourceRequestCoordBridge

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.SlotRead
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceRequest.SelSpec
open NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceFactorSel.SlotSpec
open NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)

/-! ## LitInfo's bitmap word is the systematic support's bitmap -/

section lit
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound

theorem value_eq_bitmap (a : PointwisePCPPAlgorithm)
    (r : PCPPRequest a.minimumArity) (k : Nat) (hk : k < (a.output r).systematicBits) :
    PCJ6e421fabe2aa4155_SourceLiteralSupport.value a r k =
      PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap ((a.output r).systematicSupport ⟨k, hk⟩) := by
  unfold PCJ6e421fabe2aa4155_SourceLiteralSupport.value
  rw [dif_pos hk]
  rfl

end lit

section
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceRequest
open NearCubicWires.RepairOrdinary NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape
variable {n : Nat} {circuit : BooleanCircuit n} {pcpp : PointwisePCPP circuit}

/-! ## One coordinate, read index by index -/

theorem read_at {V : Nat} (coordinate : Fin V → CircuitPolynomial (C10TotalDecode.Atom pcpp) 1) (j : Fin V)
    (ts : List (ℚ × Nat))
    (hmap : (coordinate j).monomials.map (fun mo => (mo.coefficient, mo.factors.map codeOfAtom)) =
      ts.map (fun t => (t.1, [t.2])))
    (k : Nat) (hk : k < (coordinate j).monomials.length) :
    ∃ hk' : k < ts.length, ((coordinate j).monomials[k]).coefficient = (ts[k]'hk').1 ∧
      ((coordinate j).monomials[k]).factors.map codeOfAtom = [(ts[k]'hk').2] := by
  have hl : (coordinate j).monomials.length = ts.length := by
    have := congrArg List.length hmap
    simpa using this
  have hk' : k < ts.length := hl ▸ hk
  have e := congrArg (fun l => l[k]?) hmap
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Option.map_some,
    Option.some.injEq, Prod.mk.injEq] at e
  exact ⟨hk', e.1, e.2⟩

theorem one_of_map {V : Nat} (coordinate : Fin V → CircuitPolynomial (C10TotalDecode.Atom pcpp) 1) (j : Fin V)
    (ts : List (ℚ × Nat))
    (hmap : (coordinate j).monomials.map (fun mo => (mo.coefficient, mo.factors.map codeOfAtom)) =
      ts.map (fun t => (t.1, [t.2])))
    (k : Nat) (hk : k < (coordinate j).monomials.length) : ((coordinate j).monomials[k]).factors.length = 1 := by
  obtain ⟨_, _, h⟩ := read_at coordinate j ts hmap k hk
  have := congrArg List.length h
  simpa using this

theorem bits_thr (L : Nat) (x : C10TotalDecode.Atom pcpp) (h : kindOf false (some x) = .orig) :
    bitsOf false L (some x) = SignedSortKey.binary (ThrSwitch.codeWidth L) (codeOfAtom x) := by
  cases x <;> simp_all [kindOf, bitsOf, codeOfAtom, ThrSwitch.codeBits]

theorem bits_sym (L : Nat) (x : C10TotalDecode.Atom pcpp) (h : kindOf true (some x) = .orig) :
    bitsOf true L (some x) = SignedSortKey.binary (SymOriginal.symCodeWidth L) (codeOfAtom x) := by
  cases x <;> simp_all [kindOf, bitsOf, codeOfAtom, SymOriginal.symCodeBits]

/-- **The slot pipeline's premises at the cursor's `σ`** (any mode): the kind is read off the cursor's flags, the flags are
exclusive, a parity slot's atom is its side's systematic atom, and a term slot's atom has the reader's code and its monomial the
reader's coefficient. -/
theorem slot_reads (mode : Bool) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hreads : CoordReads mode coordinate bits)
    (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (T : Bool → List (CircuitMonomial (C10TotalDecode.Atom pcpp) 1)) (e : Bool → C10TotalDecode.Atom pcpp)
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩)
    (m : Nat) (hm : m < (FactorLoop.monomials coordinate ph ci).length) (σ₀ : Sel)
    (hσ : selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m = some σ₀) (i : Nat) :
    kindOf mode ((FactorLoop.factorsAt coordinate ph ci m)[i]?) =
      (if fSys (facAt (some σ₀) i) then .sys else if fTerm (facAt (some σ₀) i) then .orig else .absent) ∧
    ¬ (fSys (facAt (some σ₀) i) = true ∧ fTerm (facAt (some σ₀) i) = true) ∧
    (fSys (facAt (some σ₀) i) = true → ∃ h : (if fSide (facAt (some σ₀) i) then (literalIndex (pcpp.clauses ci).right).val
        else (literalIndex (pcpp.clauses ci).left).val) < pcpp.systematicBits,
      (FactorLoop.factorsAt coordinate ph ci m)[i]? = some (C10TotalDecode.Atom.systematic ⟨_, h⟩)) ∧
    (fTerm (facAt (some σ₀) i) = true → ∃ (x : C10TotalDecode.Atom pcpp) (ts : List (ℚ × Nat))
      (hi : fIdx (facAt (some σ₀) i) < ts.length),
      (FactorLoop.factorsAt coordinate ph ci m)[i]? = some x ∧ kindOf mode (some x) = .orig ∧
      rawTerms bits (if fSide (facAt (some σ₀) i) then (literalIndex (pcpp.clauses ci).right).val
        else (literalIndex (pcpp.clauses ci).left).val) = some ts ∧
      codeOfAtom x = (ts[fIdx (facAt (some σ₀) i)]'hi).2 ∧
      CoefBridge.tco T (facAt (some σ₀) i) = (ts[fIdx (facAt (some σ₀) i)]'hi).1) := by
  obtain ⟨tsL, hrawL, hmapL, horigL⟩ := hreads (literalIndex (pcpp.clauses ci).left)
  obtain ⟨tsR, hrawR, hmapR, horigR⟩ := hreads (literalIndex (pcpp.clauses ci).right)
  have hone : ∀ (r : Bool) (j : Nat) (h : j < (T r).length), ((T r)[j]).factors.length = 1 := by
    intro r j h
    cases r with
    | false =>
      have h' : j < (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length := by rw [← hTL]; exact h
      have := one_of_map coordinate _ tsL hmapL j h'
      simpa [hTL] using this
    | true =>
      have h' : j < (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length := by rw [← hTR]; exact h
      have := one_of_map coordinate _ tsR hmapR j h'
      simpa [hTR] using this
  have horig : ∀ (r : Bool) (mo : CircuitMonomial (C10TotalDecode.Atom pcpp) 1), mo ∈ T r →
      ∀ x ∈ mo.factors, kindOf mode (some x) = .orig := by
    intro r mo hmo x hx
    cases r with
    | false => rw [hTL] at hmo; exact horigL mo hmo x hx
    | true => rw [hTR] at hmo; exact horigR mo hmo x hx
  obtain ⟨hget, hkind, hex⟩ := slot_kind mode pcpp coordinate ph ci T e hTL hTR heL heR hone horig m hm i
  obtain ⟨σ₁, hσ₁, hmem, _⟩ := factorsAt_eq pcpp coordinate ph ci T e hTL hTR heL heR m hm
  have e01 : σ₁ = σ₀ := Option.some.inj (hσ₁.symm.trans hσ)
  subst e01
  simp only [hσ] at hget hkind hex
  have hok0 := siteSel_ok ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
    (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
    (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
    (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
    (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length σ₁ hmem
  refine ⟨hkind, hex, ?_, ?_⟩
  · intro hs
    cases hf : facAt (some σ₁) i with
    | none => rw [hf] at hs; simp [fSys] at hs
    | some f =>
      cases f with
      | term r j => rw [hf] at hs; simp [fSys] at hs
      | sys r =>
        have hin : Fac.sys r ∈ σ₁.facs := List.mem_of_getElem? hf
        have hokf := hok0 _ hin
        rw [hf] at hget
        cases r with
        | false =>
          have h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits := by simpa [FacOK] using hokf
          simp only [fSide, Bool.false_eq_true, if_false]
          refine ⟨h, ?_⟩
          rw [hget]
          simp only [Option.map_some, atomF, heL h]
        | true =>
          have h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits := by simpa [FacOK] using hokf
          simp only [fSide, if_true]
          refine ⟨h, ?_⟩
          rw [hget]
          simp only [Option.map_some, atomF, heR h]
  · intro ht
    cases hf : facAt (some σ₁) i with
    | none => rw [hf] at ht; simp [fTerm] at ht
    | some f =>
      cases f with
      | sys r => rw [hf] at ht; simp [fTerm] at ht
      | term r j =>
        have hin : Fac.term r j ∈ σ₁.facs := List.mem_of_getElem? hf
        have hokf := hok0 _ hin
        rw [hf] at hget
        simp only [fSide, fIdx]
        cases r with
        | false =>
          have hj : j < (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length := by
            simpa [FacOK] using hokf
          obtain ⟨hj', hcoef, hcode⟩ := read_at coordinate _ tsL hmapL j hj
          have hjT : j < (T false).length := by rw [hTL]; exact hj
          obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (hone false j hjT)
          have e : (T false)[j]'hjT = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials[j]'hj := by
            simp only [hTL]
          have hxc : ((coordinate (literalIndex (pcpp.clauses ci).left)).monomials[j]'hj).factors = [x] := by
            rw [← e]; exact hx
          rw [hxc] at hcode
          refine ⟨x, tsL, hj', ?_, horig false _ (List.getElem_mem hjT) x (by rw [hx]; exact List.mem_singleton_self x),
            by simpa using hrawL, by simpa using hcode, ?_⟩
          · rw [hget]
            simp only [Option.map_some, atomF, List.getElem?_eq_getElem hjT, Option.bind_some, hx]
            rfl
          · simp only [CoefBridge.tco, List.getElem?_eq_getElem hjT]
            rw [e]
            simpa using hcoef
        | true =>
          have hj : j < (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length := by
            simpa [FacOK] using hokf
          obtain ⟨hj', hcoef, hcode⟩ := read_at coordinate _ tsR hmapR j hj
          have hjT : j < (T true).length := by rw [hTR]; exact hj
          obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (hone true j hjT)
          have e : (T true)[j]'hjT = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials[j]'hj := by
            simp only [hTR]
          have hxc : ((coordinate (literalIndex (pcpp.clauses ci).right)).monomials[j]'hj).factors = [x] := by
            rw [← e]; exact hx
          rw [hxc] at hcode
          refine ⟨x, tsR, hj', ?_, horig true _ (List.getElem_mem hjT) x (by rw [hx]; exact List.mem_singleton_self x),
            by simpa using hrawR, by simpa using hcode, ?_⟩
          · rw [hget]
            simp only [Option.map_some, atomF, List.getElem?_eq_getElem hjT, Option.bind_some, hx]
            rfl
          · simp only [CoefBridge.tco, List.getElem?_eq_getElem hjT]
            rw [e]
            simpa using hcoef

end

end NearCubicWires.SourceFactorSel.SlotRead

