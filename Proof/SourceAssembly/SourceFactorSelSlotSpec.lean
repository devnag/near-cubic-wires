import Proof.SourceAssembly.SourceFactorSelCoefBridge
import Proof.SourceAssembly.SourceFactorSelModes

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceFactorSel.SlotSpec
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceRequest.SelSpec
open NearCubicWires.SourceRequest.CurSpec

/-! ## Well-formed factors -/

/-- A factor is well formed at the site: a term's index is below its side's term count, a parity atom's side is
systematic. -/
def FacOK (JL JR : Nat) (sL sR : Bool) : Fac → Prop
  | .term r j => j < (if r then JR else JL)
  | .sys r => (if r then sR else sL) = true

/-- Every factor of every symbolic monomial of `A` is well formed. -/
def AllOK (JL JR : Nat) (sL sR : Bool) (A : List Sel) : Prop := ∀ σ ∈ A, ∀ f ∈ σ.facs, FacOK JL JR sL sR f

section ok
variable {JL JR : Nat} {sL sR : Bool}

theorem ok_sadd {A B : List Sel} (hA : AllOK JL JR sL sR A) (hB : AllOK JL JR sL sR B) :
    AllOK JL JR sL sR (sadd A B) := by
  intro σ hσ
  rcases List.mem_append.1 hσ with h | h
  · exact hA σ h
  · exact hB σ h

theorem ok_sscale (q : ℚ) {A : List Sel} (hA : AllOK JL JR sL sR A) : AllOK JL JR sL sR (sscale q A) := by
  intro σ hσ
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hσ
  exact hA a ha

theorem ok_smul {A B : List Sel} (hA : AllOK JL JR sL sR A) (hB : AllOK JL JR sL sR B) :
    AllOK JL JR sL sR (smul A B) := by
  intro σ hσ
  obtain ⟨x, hx, hσ'⟩ := List.mem_flatMap.1 hσ
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hσ'
  intro f hf
  rcases List.mem_append.1 hf with h | h
  · exact hA x hx f h
  · exact hB y hy f h

theorem ok_scoord (r : Bool) : AllOK JL JR sL sR (scoord r (if r then JR else JL)) := by
  intro σ hσ
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hσ
  intro f hf
  rw [List.mem_singleton.1 hf]
  exact List.mem_range.1 hi

theorem ok_satom (r : Bool) (h : (if r then sR else sL) = true) : AllOK JL JR sL sR (satom r) := by
  intro σ hσ
  rw [List.mem_singleton.1 hσ]
  intro f hf
  rw [List.mem_singleton.1 hf]
  exact h

theorem ok_sconst : AllOK JL JR sL sR sconst := by
  intro σ hσ
  rw [List.mem_singleton.1 hσ]
  intro f hf
  simp at hf

theorem ok_litSel (neg r : Bool) : AllOK JL JR sL sR (litSel neg r (if r then JR else JL)) := by
  unfold litSel
  cases neg
  · exact ok_scoord r
  · exact ok_sadd ok_sconst (ok_sscale _ (ok_scoord r))

theorem ok_penSide (s r : Bool) (hs : (if r then sR else sL) = s) :
    AllOK JL JR sL sR (penSide s r (if r then JR else JL)) := by
  unfold penSide
  cases s
  · exact ok_sadd (ok_smul (ok_scoord r) (ok_scoord r))
      (ok_sadd (ok_sscale _ (ok_smul (ok_smul (ok_scoord r) (ok_scoord r)) (ok_scoord r)))
        (ok_smul (ok_smul (ok_scoord r) (ok_scoord r)) (ok_smul (ok_scoord r) (ok_scoord r))))
  · exact ok_sadd (ok_satom r hs) (ok_sadd (ok_sscale _ (ok_smul (ok_satom r hs) (ok_scoord r)))
      (ok_smul (ok_scoord r) (ok_scoord r)))

end ok

/-- **Every factor of every site monomial is well formed.** -/
theorem siteSel_ok (ph : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) (sL sR nL nR : Bool)
    (JL JR : Nat) : AllOK JL JR sL sR (siteSel ph sL sR nL nR JL JR) := by
  cases ph with
  | penalty =>
    exact ok_sscale _ (ok_sadd (ok_penSide (JL := JL) (JR := JR) sL false (by simp))
      (ok_penSide (JL := JL) (JR := JR) sR true (by simp)))
  | moment => exact ok_smul (ok_scoord (JL := JL) (JR := JR) false) (ok_scoord false)
  | clause =>
    exact ok_sadd (ok_litSel (JL := JL) (JR := JR) nL false)
      (ok_sadd (ok_litSel nR true) (ok_sscale _ (ok_smul (ok_litSel nL false) (ok_litSel nR true))))

/-! ## The monomial's factor list is the slots' atoms -/

section real
variable {Atom : Type} (T : Bool → List (CircuitMonomial Atom 1)) (e : Bool → Atom)

/-- A slot's atom: the parity atom of its side, or the single factor of the term. -/
def atomF : Fac → Atom
  | .sys r => e r
  | .term r j => (((T r)[j]?).bind fun mo => mo.factors.head?).getD (e r)

theorem realF_snd (sL sR : Bool) (hone : ∀ (r : Bool) (j : Nat) (h : j < (T r).length), ((T r)[j]).factors.length = 1)
    (f : Fac) (hf : FacOK (T false).length (T true).length sL sR f) : (realF T e f).2 = [atomF T e f] := by
  cases f with
  | sys r => rfl
  | term r j =>
    have hj : j < (T r).length := by cases r <;> simpa [FacOK] using hf
    have h1 := hone r j hj
    have hg : (T r)[j]? = some ((T r)[j]) := List.getElem?_eq_getElem hj
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    simp only [realF, atomF, hg, Option.bind_some, ha]
    rfl

theorem flat_eq (sL sR : Bool)
    (hone : ∀ (r : Bool) (j : Nat) (h : j < (T r).length), ((T r)[j]).factors.length = 1)
    (L : List Fac) (hok : ∀ f ∈ L, FacOK (T false).length (T true).length sL sR f) :
    L.flatMap (fun f => (realF T e f).2) = L.map (atomF T e) := by
  induction L with
  | nil => rfl
  | cons f fs ih =>
    rw [List.flatMap_cons, List.map_cons, realF_snd T e sL sR hone f (hok f List.mem_cons_self),
      ih (fun g hg => hok g (List.mem_cons_of_mem f hg))]
    rfl

/-- **The monomial's factors are the slots' atoms**, in order. -/
theorem real_factors (sL sR : Bool)
    (hone : ∀ (r : Bool) (j : Nat) (h : j < (T r).length), ((T r)[j]).factors.length = 1)
    (σ : Sel) (hok : ∀ f ∈ σ.facs, FacOK (T false).length (T true).length sL sR f) :
    (real T e σ).2 = σ.facs.map (atomF T e) := by
  show σ.facs.flatMap (fun f => (realF T e f).2) = _
  exact flat_eq T e sL sR hone σ.facs hok

theorem real_factor_get (sL sR : Bool)
    (hone : ∀ (r : Bool) (j : Nat) (h : j < (T r).length), ((T r)[j]).factors.length = 1)
    (σ : Sel) (hok : ∀ f ∈ σ.facs, FacOK (T false).length (T true).length sL sR f) (i : Nat) :
    (real T e σ).2[i]? = (facAt (some σ) i).map (atomF T e) := by
  rw [real_factors T e sL sR hone σ hok, List.getElem?_map]
  rfl

end real

/-! ## At the consumer: `factorsAt m`'s slot `i` and its kind -/

section site
open NearCubicWires.RepairOrdinary NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceFactorSel.Modes (kindOf)
variable {n : Nat} {circuit : BooleanCircuit n}

theorem factorsAt_eq (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (e : Bool → RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic
        ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic
        ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩)
    (m : Nat) (hm : m < (SourceRequest.FactorLoop.monomials coordinate ph ci).length) :
    ∃ σ₀ : Sel, selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
        (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
        (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
        (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
        (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m = some σ₀ ∧
      σ₀ ∈ siteSel ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
        (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
        (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
        (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
        (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length ∧
      SourceRequest.FactorLoop.factorsAt coordinate ph ci m = (real T e σ₀).2 := by
  have hp := site_pairs T e pcpp coordinate RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ph ci hTL hTR
    heL heR
  set P := CloseoutFinalC10Exactness.sitePolynomial ph pcpp coordinate
    RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ci with hP
  set L := siteSel ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length with hL
  have hmon : SourceRequest.FactorLoop.monomials coordinate ph ci =
      P.monomials.map (CircuitMonomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))) := rfl
  have hmP : m < P.monomials.length := by
    have := hm
    rw [hmon, List.length_map] at this
    exact this
  have hmL : m < L.length := by
    have := congrArg List.length hp
    rw [List.length_map, List.length_map] at this
    omega
  have hpm : pairOf P.monomials[m] = real T e L[m] := by
    have := congrArg (fun l => l[m]?) hp
    simp only [List.getElem?_map, List.getElem?_eq_getElem hmP, List.getElem?_eq_getElem hmL, Option.map_some,
      Option.some.injEq] at this
    exact this
  refine ⟨L[m], List.getElem?_eq_getElem hmL, List.getElem_mem hmL, ?_⟩
  rw [SourceRequest.FactorLoop.factorsAt_of_lt coordinate ph ci m hm]
  have hget : (SourceRequest.FactorLoop.monomials coordinate ph ci)[m] =
      CircuitMonomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ)) P.monomials[m] := by
    simp only [hmon, List.getElem_map]
  rw [hget]
  exact congrArg Prod.snd hpm

/-- **The slot data the pipeline needs**, at the cursor's `σ` (every coordinate monomial a single atom of the mode's kind): slot `i`'s
factor is the cursor's slot mapped by `atomF`, its kind is read off the cursor's flags, and the flags are exclusive. -/
theorem slot_kind (mode : Bool) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (e : Bool → RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic
        ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic
        ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩)
    (hone : ∀ (r : Bool) (j : Nat) (h : j < (T r).length), ((T r)[j]).factors.length = 1)
    (horig : ∀ (r : Bool) (mo : CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1), mo ∈ T r →
      ∀ a ∈ mo.factors, kindOf mode (some a) = .orig)
    (m : Nat) (hm : m < (SourceRequest.FactorLoop.monomials coordinate ph ci).length) (i : Nat) :
    let σ := selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m
    (SourceRequest.FactorLoop.factorsAt coordinate ph ci m)[i]? = (facAt σ i).map (atomF T e) ∧
      kindOf mode ((SourceRequest.FactorLoop.factorsAt coordinate ph ci m)[i]?) =
        (if fSys (facAt σ i) then .sys else if fTerm (facAt σ i) then .orig else .absent) ∧
      ¬ (fSys (facAt σ i) = true ∧ fTerm (facAt σ i) = true) := by
  intro σ
  obtain ⟨σ₀, hσ, hmem, hfac⟩ := factorsAt_eq pcpp coordinate ph ci T e hTL hTR heL heR m hm
  have hlenL : (T false).length = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length := by rw [hTL]
  have hlenR : (T true).length = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length := by rw [hTR]
  have hok0 := siteSel_ok ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
    (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
    (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
    (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
    (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length σ₀ hmem
  rw [← hlenL, ← hlenR] at hok0
  have hget := real_factor_get T e _ _ hone σ₀ hok0 i
  have hσ' : σ = some σ₀ := hσ
  rw [hfac, hget, hσ']
  refine ⟨rfl, ?_, ?_⟩
  · cases hf : facAt (some σ₀) i with
    | none => rfl
    | some f =>
      have hin : f ∈ σ₀.facs := List.mem_of_getElem? hf
      have hokf := hok0 f hin
      cases f with
      | sys r =>
        simp only [Option.map_some, fSys, if_true]
        cases r with
        | false =>
          have h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits := by simpa [FacOK] using hokf
          show kindOf mode (some (e false)) = .sys
          rw [heL h]; rfl
        | true =>
          have h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits := by simpa [FacOK] using hokf
          show kindOf mode (some (e true)) = .sys
          rw [heR h]; rfl
      | term r j =>
        simp only [Option.map_some, fSys, fTerm, Bool.false_eq_true, if_false, if_true]
        have hj : j < (T r).length := by cases r <;> simpa [FacOK] using hokf
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hone r j hj)
        have hat : atomF T e (.term r j) = a := by
          simp only [atomF, List.getElem?_eq_getElem hj, Option.bind_some, ha]
          rfl
        rw [hat]
        exact horig r _ (List.getElem_mem hj) a (by rw [ha]; exact List.mem_singleton_self a)
  · cases facAt (some σ₀) i with
    | none => simp [fSys]
    | some f => cases f <;> simp [fSys, fTerm]

end site

end NearCubicWires.SourceFactorSel.SlotSpec

