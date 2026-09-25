import Proof.SourceAssembly.SourceRequestMonomialSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SelSpec
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceRequest.MonomialSpec

/-- Provenance of one factor: the systematic parity atom of the left (`false`) / right (`true`) literal, or term `idx`
of that literal's guessed sum. -/
inductive Fac where
  | sys (right : Bool)
  | term (right : Bool) (idx : Nat)
  deriving DecidableEq

/-- A symbolic monomial: factor provenances in order, and the constant multiplier. -/
structure Sel where
  facs : List Fac
  rho : ℚ

def smul1 (a b : Sel) : Sel := ⟨a.facs ++ b.facs, a.rho * b.rho⟩
def sadd (A B : List Sel) : List Sel := A ++ B
def smul (A B : List Sel) : List Sel := A.flatMap fun a => B.map (smul1 a)
def sscale (q : ℚ) (A : List Sel) : List Sel := A.map fun a => ⟨a.facs, q * a.rho⟩
def sconst : List Sel := [⟨[], 1⟩]
def satom (r : Bool) : List Sel := [⟨[.sys r], 1⟩]
def scoord (r : Bool) (J : Nat) : List Sel := (List.range J).map fun i => ⟨[.term r i], 1⟩

section real
variable {Atom : Type} (T : Bool → List (CircuitMonomial Atom 1)) (e : Bool → Atom)

/-- One factor's value: `(coefficient, factor list)`. -/
def realF : Fac → ℚ × List Atom
  | .sys r => (1, [e r])
  | .term r i => match (T r)[i]? with
    | some mo => (mo.coefficient, mo.factors)
    | none => (0, [])

/-- A symbolic monomial's value: its multiplier times its factors' coefficients, factor lists concatenated. -/
def real (σ : Sel) : ℚ × List Atom :=
  (σ.rho * (σ.facs.map fun f => (realF T e f).1).prod, σ.facs.flatMap fun f => (realF T e f).2)

def pairOf {d : Nat} (mo : CircuitMonomial Atom d) : ℚ × List Atom := (mo.coefficient, mo.factors)

theorem real_smul1 (a b : Sel) :
    real T e (smul1 a b) = ((real T e a).1 * (real T e b).1, (real T e a).2 ++ (real T e b).2) := by
  unfold real smul1
  simp only [List.map_append, List.prod_append, List.flatMap_append, Prod.mk.injEq, and_true]
  ring

theorem pairs_add {d : Nat} (A B : CircuitPolynomial Atom d) :
    (A.add B).monomials.map pairOf = A.monomials.map pairOf ++ B.monomials.map pairOf :=
  List.map_append

theorem pairs_scale {d : Nat} (q : ℚ) (A : CircuitPolynomial Atom d) :
    (A.scale q).monomials.map pairOf = (A.monomials.map pairOf).map fun p => (q * p.1, p.2) := by
  show ((A.monomials.map (CircuitMonomial.scale q)).map pairOf) = _
  rw [List.map_map, List.map_map]
  rfl

theorem pairs_weaken {d d' : Nat} (h : d ≤ d') (A : CircuitPolynomial Atom d) :
    (A.weaken h).monomials.map pairOf = A.monomials.map pairOf := by
  show ((A.monomials.map (CircuitMonomial.weaken h)).map pairOf) = _
  rw [List.map_map]
  rfl

theorem pairs_mul {d d' : Nat} (A : CircuitPolynomial Atom d) (B : CircuitPolynomial Atom d') :
    (A.mul B).monomials.map pairOf =
      (A.monomials.map pairOf).flatMap fun p => (B.monomials.map pairOf).map fun p' => (p.1 * p'.1, p.2 ++ p'.2) := by
  show (A.monomials.flatMap fun a => B.monomials.map a.mul).map pairOf = _
  rw [List.map_flatMap, List.flatMap_map]
  congr 1
  funext a
  rw [List.map_map, List.map_map]
  rfl

/-- `pairs_mul` at literal result degrees (where the ambient type fixed the degree as a numeral). -/
theorem pairs_mul_2 (A B : CircuitPolynomial Atom 1) :
    (A.mul B).monomials.map (@pairOf Atom 2) =
      (A.monomials.map pairOf).flatMap fun p => (B.monomials.map pairOf).map fun p' => (p.1 * p'.1, p.2 ++ p'.2) :=
  pairs_mul A B

theorem pairs_mul_4 (A B : CircuitPolynomial Atom 2) :
    (A.mul B).monomials.map (@pairOf Atom 4) =
      (A.monomials.map pairOf).flatMap fun p => (B.monomials.map pairOf).map fun p' => (p.1 * p'.1, p.2 ++ p'.2) :=
  pairs_mul A B

theorem pairs_mul_3 (A : CircuitPolynomial Atom 2) (B : CircuitPolynomial Atom 1) :
    (A.mul B).monomials.map (@pairOf Atom 3) =
      (A.monomials.map pairOf).flatMap fun p => (B.monomials.map pairOf).map fun p' => (p.1 * p'.1, p.2 ++ p'.2) :=
  pairs_mul A B

theorem real_add (A B : List Sel) : (sadd A B).map (real T e) = A.map (real T e) ++ B.map (real T e) :=
  List.map_append

theorem real_scale (q : ℚ) (A : List Sel) :
    (sscale q A).map (real T e) = (A.map (real T e)).map fun p => (q * p.1, p.2) := by
  unfold sscale
  rw [List.map_map, List.map_map]
  congr 1
  funext a
  simp only [Function.comp, real, Prod.mk.injEq, and_true]
  ring

theorem real_mul (A B : List Sel) :
    (smul A B).map (real T e) =
      (A.map (real T e)).flatMap fun p => (B.map (real T e)).map fun p' => (p.1 * p'.1, p.2 ++ p'.2) := by
  unfold smul
  rw [List.map_flatMap, List.flatMap_map]
  congr 1
  funext a
  rw [List.map_map, List.map_map]
  congr 1
  funext b
  simp only [Function.comp]
  exact real_smul1 T e a b

/-- A coordinate IS its symbolic coordinate (every monomial is recovered by index). -/
theorem real_coord (r : Bool) :
    (scoord r (T r).length).map (real T e) = (T r).map pairOf := by
  unfold scoord
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp, real, realF,
      List.getElem?_eq_getElem (by simpa using h1), List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, mul_one, one_mul, pairOf]

theorem real_atom (r : Bool) : (satom r).map (real T e) = [(1, [e r])] := by
  simp [satom, real, realF]

theorem real_const : sconst.map (real T e) = [(1, [])] := by
  simp [sconst, real]

end real

/-! ## The three site lists, symbolically -/

def litSel (neg r : Bool) (J : Nat) : List Sel :=
  if neg then sadd sconst (sscale (-1) (scoord r J)) else scoord r J

def penSide (sys r : Bool) (J : Nat) : List Sel :=
  if sys then sadd (satom r) (sadd (sscale (-2) (smul (satom r) (scoord r J))) (smul (scoord r J) (scoord r J)))
  else sadd (smul (scoord r J) (scoord r J))
    (sadd (sscale (-2) (smul (smul (scoord r J) (scoord r J)) (scoord r J)))
      (smul (smul (scoord r J) (scoord r J)) (smul (scoord r J) (scoord r J))))

open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule in
/-- **The site list, symbolically** (before the uniform `1/2^clauseBits`). -/
def siteSel : Phase → Bool → Bool → Bool → Bool → Nat → Nat → List Sel
  | .penalty, sL, sR, _, _, JL, JR => sscale (1 / 2) (sadd (penSide sL false JL) (penSide sR true JR))
  | .moment, _, _, _, _, JL, _ => smul (scoord false JL) (scoord false JL)
  | .clause, _, _, nL, nR, JL, JR =>
    sadd (litSel nL false JL) (sadd (litSel nR true JR) (sscale (-1) (smul (litSel nL false JL) (litSel nR true JR))))

section site
variable {Atom : Type} (T : Bool → List (CircuitMonomial Atom 1)) (e : Bool → Atom)

theorem real_coordOf (r : Bool) (P : CircuitPolynomial Atom 1) (hP : T r = P.monomials) :
    (scoord r P.monomials.length).map (real T e) = P.monomials.map pairOf := by
  rw [← hP]; exact real_coord T e r

theorem pairs_const : (CircuitPolynomial.constant (Circuit := Atom) 1 1).monomials.map pairOf = [(1, [])] := rfl

theorem pairs_atom (x : Atom) : (atomPolynomial x).monomials.map pairOf = [(1, [x])] := rfl

theorem lit_pairs (neg r : Bool) (P : CircuitPolynomial Atom 1) (hP : T r = P.monomials) :
    (literalPolynomial neg P).monomials.map pairOf = (litSel neg r P.monomials.length).map (real T e) := by
  cases neg
  · show P.monomials.map pairOf = (scoord r P.monomials.length).map (real T e)
    rw [real_coordOf T e r P hP]
  · show ((CircuitPolynomial.constant 1 1).add (P.scale (-1))).monomials.map pairOf = _
    unfold litSel
    rw [if_pos rfl, pairs_add, pairs_scale, pairs_const, real_add, real_scale, real_const, real_coordOf T e r P hP]

theorem sysValidity_pairs (r : Bool) (P : CircuitPolynomial Atom 1) (hP : T r = P.monomials) :
    (systematicValidityPolynomial (e r) P).monomials.map pairOf =
      (penSide true r P.monomials.length).map (real T e) := by
  unfold systematicValidityPolynomial penSide
  rw [if_pos rfl]
  simp only [pairs_add, pairs_scale, pairs_weaken]
  repeat rw [pairs_mul_2]
  simp only [pairs_atom, real_add, real_scale, real_mul, real_atom, real_coordOf T e r P hP]

theorem auxValidity_pairs (r : Bool) (P : CircuitPolynomial Atom 1) (hP : T r = P.monomials) :
    (auxiliaryValidityPolynomial P).monomials.map pairOf =
      (penSide false r P.monomials.length).map (real T e) := by
  unfold auxiliaryValidityPolynomial penSide
  rw [if_neg (by decide)]
  simp only [pairs_add, pairs_scale, pairs_weaken]
  repeat (first | rw [pairs_mul_4] | rw [pairs_mul_3] | rw [pairs_mul_2] | rw [pairs_mul])
  simp only [real_add, real_scale, real_mul, real_coordOf T e r P hP]

end site

section site2
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape
variable {Atom : Type} (T : Bool → List (CircuitMonomial Atom 1)) (e : Bool → Atom)
  {n : Nat} {circuit : BooleanCircuit n}

theorem pen_pairs (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (sa : Fin pcpp.systematicBits → Atom) (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) (r : Bool)
    (hT : T r = (coordinate j).monomials) (he : ∀ h : j.val < pcpp.systematicBits, e r = sa ⟨j.val, h⟩) :
    (coordinatePenalty pcpp coordinate sa j).monomials.map pairOf =
      (penSide (decide (j.val < pcpp.systematicBits)) r (coordinate j).monomials.length).map (real T e) := by
  cases j using Fin.addCases with
  | left i =>
    unfold coordinatePenalty
    rw [Fin.addCases_left, pairs_weaken]
    have hi : (Fin.castAdd pcpp.auxiliaryBits i).val < pcpp.systematicBits := by simp
    have hd : decide ((Fin.castAdd pcpp.auxiliaryBits i).val < pcpp.systematicBits) = true := by simp
    rw [hd]
    have he' : e r = sa i := by rw [he hi]; rfl
    rw [← he']
    exact sysValidity_pairs T e r _ hT
  | right i =>
    unfold coordinatePenalty
    rw [Fin.addCases_right]
    have hd : decide ((Fin.natAdd pcpp.systematicBits i).val < pcpp.systematicBits) = false := by simp
    rw [hd]
    exact auxValidity_pairs T e r _ hT

/-- **The site list IS the symbolic one under `real`** (before `siteCalls`' uniform `1/2^clauseBits`). -/
theorem site_pairs (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (sa : Fin pcpp.systematicBits → Atom) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = sa ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = sa ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩) :
    (sitePolynomial ph pcpp coordinate sa ci).monomials.map pairOf =
      (siteSel ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
        (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
        (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
        (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
        (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length).map (real T e) := by
  cases ph with
  | penalty =>
    show (CircuitPolynomial.scale (1 / 2) ((coordinatePenalty pcpp coordinate sa _).add
      (coordinatePenalty pcpp coordinate sa _))).monomials.map pairOf = _
    rw [pairs_scale, pairs_add, pen_pairs T e pcpp coordinate sa _ false hTL heL,
      pen_pairs T e pcpp coordinate sa _ true hTR heR]
    show _ = (sscale (1 / 2) (sadd _ _)).map (real T e)
    rw [real_scale, real_add]
  | moment =>
    show ((secondMomentPolynomial (coordinate _)).weaken _).monomials.map pairOf = _
    rw [pairs_weaken]
    show ((coordinate _).mul (coordinate _)).monomials.map (@pairOf Atom 2) = _
    rw [pairs_mul_2]
    show _ = (smul (scoord false _) (scoord false _)).map (real T e)
    rw [real_mul, real_coordOf T e false _ hTL]
  | clause =>
    show ((clausePolynomial _ _ (coordinate _) (coordinate _)).weaken _).monomials.map pairOf = _
    rw [pairs_weaken]
    unfold clausePolynomial
    simp only [pairs_add, pairs_weaken, pairs_scale]
    rw [pairs_mul_2, lit_pairs T e _ false _ hTL, lit_pairs T e _ true _ hTR]
    show _ = (sadd (litSel _ false _) (sadd (litSel _ true _) (sscale (-1) (smul (litSel _ false _)
      (litSel _ true _))))).map (real T e)
    rw [real_add, real_add, real_scale, real_mul]

end site2

end NearCubicWires.SourceRequest.SelSpec

