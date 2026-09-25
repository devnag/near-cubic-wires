import Proof.SourceAssembly.SourceFactorSelSlotRead

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.KBridge
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceRequest.SelSpec
open NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceFactorSel.SlotSpec NearCubicWires.SourceFactorSel.SlotRead
open NearCubicWires.SourceRequest.CoordBridge

section
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceRequest
open NearCubicWires.RepairOrdinary NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape
variable {n : Nat} {circuit : BooleanCircuit n}

/-- **The header's count is the cursor's `k`.** -/
theorem factorsAt_len (mode : Bool) (pcpp : PointwisePCPP circuit)
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
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length) :
    (FactorLoop.factorsAt coordinate ph ci m).length =
      kOf (selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
        (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
        (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
        (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
        (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m) := by
  obtain ⟨tsL, _, hmapL, _⟩ := hreads (literalIndex (pcpp.clauses ci).left)
  obtain ⟨tsR, _, hmapR, _⟩ := hreads (literalIndex (pcpp.clauses ci).right)
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
  rcases Nat.lt_or_ge m (FactorLoop.monomials coordinate ph ci).length with hlt | hge
  · obtain ⟨σ₀, hσ, hmem, hfac⟩ := factorsAt_eq pcpp coordinate ph ci T e hTL hTR heL heR m hlt
    have hok0 := siteSel_ok ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length σ₀ hmem
    have hlenL : (T false).length = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length := by rw [hTL]
    have hlenR : (T true).length = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length := by rw [hTR]
    rw [← hlenL, ← hlenR] at hok0
    rw [hfac, hσ, real_factors T e _ _ hone σ₀ hok0, List.length_map]
    rfl
  · have hmN : m = (FactorLoop.monomials coordinate ph ci).length := le_antisymm hm hge
    have hp := site_pairs T e pcpp coordinate C10TotalDecode.Atom.systematic ph ci hTL hTR heL heR
    have hlen := congrArg List.length hp
    rw [List.length_map, List.length_map] at hlen
    have hmon : (FactorLoop.monomials coordinate ph ci).length = (CloseoutFinalC10Exactness.sitePolynomial ph pcpp
        coordinate C10TotalDecode.Atom.systematic ci).monomials.length := by
      show (List.map _ _).length = _
      rw [List.length_map]
    rw [hmN, FactorLoop.factorsAt_end]
    unfold selAt
    rw [List.getElem?_eq_none (by rw [← hlen, ← hmon])]
    rfl

end

end NearCubicWires.SourceFactorSel.KBridge

