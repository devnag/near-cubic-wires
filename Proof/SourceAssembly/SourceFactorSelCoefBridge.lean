import Proof.SourceAssembly.SourceFactorSelCoefR
import Proof.SourceAssembly.SourceRequestCurSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceFactorSel.CoefBridge
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceRequest.SelSpec
open NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceFactorSel.CoefValue NearCubicWires.SourceFactorSel.CoefR

/-! ## At most four factors -/

/-- Every symbolic monomial of `A` has at most `k` factors. -/
def FacsLe (k : Nat) (A : List Sel) : Prop := ∀ σ ∈ A, σ.facs.length ≤ k

theorem facsLe_mono {k k' : Nat} {A : List Sel} (h : FacsLe k A) (hk : k ≤ k') : FacsLe k' A :=
  fun σ hσ => (h σ hσ).trans hk

theorem facsLe_sadd {k : Nat} {A B : List Sel} (hA : FacsLe k A) (hB : FacsLe k B) : FacsLe k (sadd A B) := by
  intro σ hσ
  rcases List.mem_append.1 hσ with h | h
  · exact hA σ h
  · exact hB σ h

theorem facsLe_sscale {k : Nat} (q : ℚ) {A : List Sel} (hA : FacsLe k A) : FacsLe k (sscale q A) := by
  intro σ hσ
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hσ
  exact hA a ha

theorem facsLe_smul {a b : Nat} {A B : List Sel} (hA : FacsLe a A) (hB : FacsLe b B) : FacsLe (a + b) (smul A B) := by
  intro σ hσ
  obtain ⟨x, hx, hσ'⟩ := List.mem_flatMap.1 hσ
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hσ'
  show (x.facs ++ y.facs).length ≤ a + b
  rw [List.length_append]
  exact Nat.add_le_add (hA x hx) (hB y hy)

theorem facsLe_scoord (r : Bool) (J : Nat) : FacsLe 1 (scoord r J) := by
  intro σ hσ
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hσ
  exact Nat.le_refl 1

theorem facsLe_satom (r : Bool) : FacsLe 1 (satom r) := by
  intro σ hσ
  rw [List.mem_singleton.1 hσ]
  exact Nat.le_refl 1

theorem facsLe_sconst : FacsLe 0 sconst := by
  intro σ hσ
  rw [List.mem_singleton.1 hσ]
  exact Nat.le_refl 0

theorem facsLe_litSel (neg r : Bool) (J : Nat) : FacsLe 1 (litSel neg r J) := by
  unfold litSel
  cases neg
  · exact facsLe_scoord r J
  · exact facsLe_sadd (facsLe_mono facsLe_sconst (by decide)) (facsLe_sscale _ (facsLe_scoord r J))

theorem facsLe_penSide (sys r : Bool) (J : Nat) : FacsLe 4 (penSide sys r J) := by
  unfold penSide
  cases sys
  · exact facsLe_sadd (facsLe_mono (facsLe_smul (facsLe_scoord r J) (facsLe_scoord r J)) (by decide))
      (facsLe_sadd (facsLe_mono (facsLe_sscale _ (facsLe_smul (facsLe_smul (facsLe_scoord r J) (facsLe_scoord r J))
        (facsLe_scoord r J))) (by decide))
        (facsLe_smul (facsLe_smul (facsLe_scoord r J) (facsLe_scoord r J))
          (facsLe_smul (facsLe_scoord r J) (facsLe_scoord r J))))
  · exact facsLe_sadd (facsLe_mono (facsLe_satom r) (by decide))
      (facsLe_sadd (facsLe_mono (facsLe_sscale _ (facsLe_smul (facsLe_satom r) (facsLe_scoord r J))) (by decide))
        (facsLe_mono (facsLe_smul (facsLe_scoord r J) (facsLe_scoord r J)) (by decide)))

/-- **Every monomial of every site has at most four factors** (so four cursor slots suffice). -/
theorem siteSel_facs (ph : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) (sL sR nL nR : Bool)
    (JL JR : Nat) : FacsLe 4 (siteSel ph sL sR nL nR JL JR) := by
  cases ph with
  | penalty => exact facsLe_sscale _ (facsLe_sadd (facsLe_penSide sL false JL) (facsLe_penSide sR true JR))
  | moment => exact facsLe_mono (facsLe_smul (facsLe_scoord false JL) (facsLe_scoord false JL)) (by decide)
  | clause =>
    exact facsLe_sadd (facsLe_mono (facsLe_litSel nL false JL) (by decide))
      (facsLe_sadd (facsLe_mono (facsLe_litSel nR true JR) (by decide))
        (facsLe_mono (facsLe_sscale _ (facsLe_smul (facsLe_litSel nL false JL) (facsLe_litSel nR true JR)))
          (by decide)))

/-! ## `real`'s coefficient over four slots -/

section real4
variable {Atom : Type} (T : Bool → List (CircuitMonomial Atom 1)) (e : Bool → Atom)

/-- A slot's term coefficient (`0` if the slot is not a term; never read then). -/
def tco : Option Fac → ℚ
  | some (.term r j) => (((T r)[j]?).map (fun mo => mo.coefficient)).getD 0
  | _ => 0

theorem realF_fst (x : Fac) : (realF T e x).1 = u (fTerm (some x)) (tco T (some x)) := by
  cases x with
  | sys r => rfl
  | term r j =>
    unfold realF
    cases h : (T r)[j]? with
    | none => simp [u, tco, fTerm, h]
    | some mo => simp [u, tco, fTerm, h]

theorem prod_four {α : Type} (g : α → ℚ) (L : List α) (h : L.length ≤ 4) :
    (L.map g).prod = ∏ i : Fin 4, ((L[i.val]?).map g).getD 1 := by
  rw [Fin.prod_univ_four]
  match L, h with
  | [], _ => simp
  | [a], _ => simp
  | [a, b], _ => simp
  | [a, b, c], _ => simp [mul_assoc]
  | [a, b, c, d], _ => simp [mul_assoc]
  | _ :: _ :: _ :: _ :: _ :: _, h =>
    exfalso
    simp only [List.length_cons] at h
    omega

/-- **A symbolic monomial's coefficient over the four cursor slots.** -/
theorem real_prod4 (σ : Sel) (h : σ.facs.length ≤ 4) :
    (real T e σ).1 = σ.rho * ∏ i : Fin 4, u (fTerm (facAt (some σ) i)) (tco T (facAt (some σ) i)) := by
  show σ.rho * (σ.facs.map fun f => (realF T e f).1).prod = _
  rw [prod_four _ _ h]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  show ((σ.facs[i.val]?).map fun f => (realF T e f).1).getD 1 =
    u (fTerm (σ.facs[i.val]?)) (tco T (σ.facs[i.val]?))
  cases hx : σ.facs[i.val]? with
  | none => rfl
  | some x => exact realF_fst T e x

end real4

/-! ## The bridge -/

section bridge
open NearCubicWires.RepairOrdinary NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape
variable {n : Nat} {circuit : BooleanCircuit n}

theorem coef_bridge (pcpp : PointwisePCPP circuit)
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
    let σ := selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m
    ((SourceRequest.FactorLoop.monomials coordinate ph ci)[m]).coefficient =
      coefOfR (2 ^ pcpp.clauseBits) ((σ.map Sel.rho).getD 0) (fun i => fTerm (facAt σ i))
        (fun i => tco T (facAt σ i)) := by
  intro σ
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
  have hσ : σ = some L[m] := List.getElem?_eq_getElem hmL
  have hpm : pairOf P.monomials[m] = real T e L[m] := by
    have := congrArg (fun l => l[m]?) hp
    simp only [List.getElem?_map, List.getElem?_eq_getElem hmP, List.getElem?_eq_getElem hmL, Option.map_some,
      Option.some.injEq] at this
    exact this
  have hc : P.monomials[m].coefficient = (real T e L[m]).1 := congrArg Prod.fst hpm
  have h4 : L[m].facs.length ≤ 4 := siteSel_facs _ _ _ _ _ _ _ L[m] (List.getElem_mem hmL)
  have hget : (SourceRequest.FactorLoop.monomials coordinate ph ci)[m] =
      CircuitMonomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ)) P.monomials[m] := by
    simp only [hmon, List.getElem_map]
  rw [hget]
  show (1 / (2 ^ pcpp.clauseBits : ℚ)) * P.monomials[m].coefficient = _
  rw [hc, real_prod4 T e L[m] h4, hσ]
  unfold coefOfR
  push_cast
  rfl

/-- **The `coefT` conjunct in the consumer's own words**: whatever writes `coefWord b R (coefOfR …)` of the cursor's data
(e.g. `CoefR.coefR_step`) writes `FactorSelection.select`'s coefficient words for monomial `m`. -/
theorem coefT_conj {U : Nat} (pcpp : PointwisePCPP circuit)
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
    (m : Nat) (hm : m < (SourceRequest.FactorLoop.monomials coordinate ph ci).length)
    (b R : Nat) (A' : Fin U → List Bool) (coefT : Fin 3 → Fin U)
    (h : ∀ i : Fin 3, A' (coefT i) = SourceFactorSel.Coef.coefWord b R
      (coefOfR (2 ^ pcpp.clauseBits)
        (((selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
          (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
          (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
          (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
          (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m).map Sel.rho).getD 0)
        (fun i => fTerm (facAt (selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
          (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
          (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
          (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
          (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m) i))
        (fun i => tco T (facAt (selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
          (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
          (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
          (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
          (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m) i))) i) :
    ∀ i : Fin 3, A' (coefT i) = ZeroPadding.pad R (RepairOrdinary.frame
      (RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.recordFields b
        (RepairOrdinary.CloseoutFinalC10SupplierCalls.coefficientEstimate
          ((SourceRequest.FactorLoop.monomials coordinate ph ci)[m]).coefficient) 0 0 ⟨i.val, by omega⟩)) := by
  intro i
  rw [h i, ← coef_bridge pcpp coordinate ph ci T e hTL hTR heL heR m hm]
  rfl

end bridge

end NearCubicWires.SourceFactorSel.CoefBridge

