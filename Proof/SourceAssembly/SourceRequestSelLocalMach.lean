import Proof.SourceAssembly.SourceRequestSelBackThrRun

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open PCJ6e421fabe2aa4155_SourceLiteralSupport (value)
noncomputable section

/-! ## The `36 ↔ 39` swap and front A's dock -/

/-- The swap on values. -/
def swv (k : Nat) : Nat := if k = 36 then 39 else if k = 39 then 36 else k

theorem swv_swv (k : Nat) : swv (swv k) = k := by
  by_cases h1 : k = 36
  · subst h1; decide
  · by_cases h2 : k = 39
    · subst h2; decide
    · simp only [swv, if_neg h1, if_neg h2]

theorem swv_ne (k : Nat) (h1 : k ≠ 36) (h2 : k ≠ 39) : swv k = k := by
  simp only [swv, if_neg h1, if_neg h2]

theorem swv_lt (k : Nat) (h : k < NF) : swv k < NF := by
  by_cases h1 : k = 36
  · subst h1; decide
  · by_cases h2 : k = 39
    · subst h2; decide
    · rw [swv_ne k h1 h2]; exact h

/-- A value kept by front A (`< 100` or `≥ 202`) stays in that range under the swap. -/
theorem swv_keep (k : Nat) (h : k < 100 ∨ 202 ≤ k) : swv k < 100 ∨ 202 ≤ swv k := by
  by_cases h1 : k = 36
  · subst h1; decide
  · by_cases h2 : k = 39
    · subst h2; decide
    · rw [swv_ne k h1 h2]; exact h

def sw (z : Fin NF) : Fin NF := ⟨swv z.val, swv_lt z.val z.isLt⟩

theorem sw_sw (z : Fin NF) : sw (sw z) = z := Fin.ext (swv_swv z.val)

theorem sw_ne (z : Fin NF) (h1 : z.val ≠ 36) (h2 : z.val ≠ 39) : sw z = z := Fin.ext (swv_ne z.val h1 h2)

/-- Front A's dock: the fixed ports, `36` and `39` exchanged. -/
def us {t : Nat} (z : Fin NF) : Fin (NF + (19 + 4 * t)) := up (sw z)

theorem up_inj {t : Nat} : Function.Injective (up (t := t)) := by
  intro x y h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [up_val, up_val] at hv
  exact hv

theorem us_inj {t : Nat} : Function.Injective (us (t := t)) := by
  intro x y h
  have h1 : sw x = sw y := up_inj h
  have h2 := congrArg sw h1
  rwa [sw_sw, sw_sw] at h2

theorem up_us {t : Nat} (z : Fin NF) : up (t := t) z = us (sw z) := by
  unfold us; rw [sw_sw]

/-! ## The request-free back docks (THR) -/

/-- The THR producer's tape count, with no request data. -/
abbrev tT (da : RepairRepresentation.DecompositionAlgorithm) : Nat := 3864 + 2 * ThrOriginal.Tn da

theorem slotT_lt (da : RepairRepresentation.DecompositionAlgorithm) (i : Fin 4) (j : Fin (tT da)) :
    19 + i.val * tT da + j.val < 19 + 4 * tT da := by
  have hi := i.isLt
  have hj := j.isLt
  have h := Nat.mul_le_mul_right (tT da) (show i.val + 1 ≤ 4 by omega)
  rw [Nat.succ_mul] at h
  omega

def loT (da : RepairRepresentation.DecompositionAlgorithm) (k : Nat) (h : k < NF) : Fin (NF + (19 + 4 * tT da)) :=
  Fin.castAdd _ ⟨k, h⟩
def rgT (da : RepairRepresentation.DecompositionAlgorithm) (x : Fin (19 + 4 * tT da)) : Fin (NF + (19 + 4 * tT da)) :=
  Fin.natAdd NF x
def cslotT (da : RepairRepresentation.DecompositionAlgorithm) (i : Fin 4) (j : Fin (tT da)) : Fin (19 + 4 * tT da) :=
  ⟨19 + i.val * tT da + j.val, slotT_lt da i j⟩

/-- `SelBack.slB` at the THR producer, request-free. -/
def slBT (da : RepairRepresentation.DecompositionAlgorithm) (i : Fin 4) (j : Fin 1121) : Fin (NF + (19 + 4 * tT da)) :=
  if h17 : j.val < 17 then loT da (inPort i.val j.val) (by have := inPort_lt i.val i.isLt j.val h17; unfold NF; omega)
  else if h33 : j.val < 33 then rgT da (cslotT da i (ThrSwitch.descSlots da ⟨j.val - 17, by omega⟩))
  else if j.val = 33 then loT da (1400 + i.val) (by have := i.isLt; unfold NF; omega)
  else loT da (1500 + 1100 * i.val + (j.val - 34)) (by have := i.isLt; have := j.isLt; unfold NF; omega)

/-- `SelBack.hdSl` at the THR producer, request-free. -/
def hdSlT (da : RepairRepresentation.DecompositionAlgorithm) (j : Fin 35) : Fin (NF + (19 + 4 * tT da)) :=
  if j.val = 0 then loT da 1222 (by decide)
  else if j.val < 5 then loT da (24 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val = 5 then loT da 31 (by decide)
  else if j.val = 6 then loT da 43 (by decide)
  else if j.val = 7 then rgT da ⟨0, by omega⟩
  else loT da (6000 + j.val) (by have := j.isLt; unfold NF; omega)

/-- `SelBack.cfSl` at the THR producer, request-free. -/
def cfSlT (da : RepairRepresentation.DecompositionAlgorithm) (j : Fin 245) : Fin (NF + (19 + 4 * tT da)) :=
  if j.val < 4 then loT da (1400 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val < 8 then loT da (1207 + 4 * (j.val - 4)) (by have := j.isLt; unfold NF; omega)
  else if j.val = 8 then loT da 1223 (by decide)
  else if j.val = 9 then loT da 32 (by decide)
  else if j.val = 10 then loT da 39 (by decide)
  else if j.val < 14 then loT da (23 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val = 14 then loT da 44 (by decide)
  else loT da (6100 + j.val) (by have := j.isLt; unfold NF; omega)

/-! ## The packed pieces and the fixed machine -/

def pA : Σ s, Machine NF s := ⟨_, frontA⟩
def pB (ph : Phase) : Σ s, Machine NF s := ⟨_, frontB ph⟩
def p4 (da : RepairRepresentation.DecompositionAlgorithm) : Σ s, Machine (NF + (19 + 4 * tT da)) s :=
  ⟨_, SourceFactorSel.Slots4.fourM (slBT da)⟩
def pH : Σ s, Machine 35 s := ⟨_, SourceFactorSel.HdrBlock.hdrM⟩
def pC : Σ s, Machine 245 s := ⟨_, SourceFactorSel.CoefR.coefRM⟩

/-- **The back machine (THR)**: four slots ; header block ; coefficient stage. -/
def backP (da : RepairRepresentation.DecompositionAlgorithm) :=
  Composition.machine (p4 da).2
    (Composition.machine (RecoveryFocus.machine (hdSlT da) pH.2) (RecoveryFocus.machine (cfSlT da) pC.2))

/-- **FactorSelection's machine on the local universe (THR, phase `ph`)**: ONE fixed machine per `(da, ph)`. -/
def selThrM (ph : Phase) (da : RepairRepresentation.DecompositionAlgorithm) :=
  Composition.machine (RecoveryFocus.machine (us (t := tT da)) pA.2)
  (Composition.machine (RecoveryFocus.machine (up (t := tT da)) (pB ph).2) (backP da))

/-- A run of the four slots at ANY request's THR producer is a run of the packed slot machine. -/
theorem four_packed {n0 : Nat} {circuit : BooleanCircuit n0} (pcpp : PointwisePCPP circuit)
    (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld n : Nat)
    (H H' : Fin (NF + (19 + 4 * tT da)) → Nat) (A A' : Fin (NF + (19 + 4 * tT da)) → List Bool)
    (s : Step (SourceFactorSel.Slots4.fourM (slB (PT (pcpp := pcpp) da Pw W Ld) rfl)) n H A H' A') :
    Step (p4 da).2 n H A H' A' := s

theorem hdr_packed {n0 : Nat} {circuit : BooleanCircuit n0} (pcpp : PointwisePCPP circuit)
    (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld n : Nat)
    (H H' : Fin (NF + (19 + 4 * tT da)) → Nat) (A A' : Fin (NF + (19 + 4 * tT da)) → List Bool)
    (s : Step (RecoveryFocus.machine (hdSl (PT (pcpp := pcpp) da Pw W Ld)) SourceFactorSel.HdrBlock.hdrM) n H A H' A') :
    Step (RecoveryFocus.machine (hdSlT da) pH.2) n H A H' A' := s

theorem coef_packed {n0 : Nat} {circuit : BooleanCircuit n0} (pcpp : PointwisePCPP circuit)
    (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld n : Nat)
    (H H' : Fin (NF + (19 + 4 * tT da)) → Nat) (A A' : Fin (NF + (19 + 4 * tT da)) → List Bool)
    (s : Step (RecoveryFocus.machine (cfSl (PT (pcpp := pcpp) da Pw W Ld)) SourceFactorSel.CoefR.coefRM) n H A H' A') :
    Step (RecoveryFocus.machine (cfSlT da) pC.2) n H A H' A' := s

theorem frontA_packed (n : Nat) (H H' : Fin NF → Nat) (A A' : Fin NF → List Bool) (s : Step frontA n H A H' A') :
    Step pA.2 n H A H' A' := s

theorem frontB_packed (ph : Phase) (n : Nat) (H H' : Fin NF → Nat) (A A' : Fin NF → List Bool)
    (s : Step (frontB ph) n H A H' A') : Step (pB ph).2 n H A H' A' := s

/-! ## Site data: the two literals' term lists and atoms -/

section site
variable {n0 : Nat} {circuit : BooleanCircuit n0}

/-- The queried clause's two coordinate term lists (`false` = left). -/
def Tof {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (ci : Fin (2 ^ pcpp.clauseBits)) : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
  | false => (coordinate (literalIndex (pcpp.clauses ci).left)).monomials
  | true => (coordinate (literalIndex (pcpp.clauses ci).right)).monomials

/-- The parity atom of a systematic index (any atom otherwise; unused there). -/
def atomAt (pcpp : PointwisePCPP circuit) (k : Nat) : RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp :=
  if h : k < pcpp.systematicBits then .systematic ⟨k, h⟩ else .symmetric ⟨0, fun i => i.elim0, fun _ => false⟩

/-- The queried clause's two parity atoms (`false` = left). -/
def eOf (pcpp : PointwisePCPP circuit) (ci : Fin (2 ^ pcpp.clauseBits)) :
    Bool → RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp
  | false => atomAt pcpp (literalIndex (pcpp.clauses ci).left).val
  | true => atomAt pcpp (literalIndex (pcpp.clauses ci).right).val

theorem atomAt_sys (pcpp : PointwisePCPP circuit) (k : Nat) (h : k < pcpp.systematicBits) :
    atomAt pcpp k = .systematic ⟨k, h⟩ := by
  unfold atomAt; rw [dif_pos h]

end site

/-- LitInfo's bitmap word is never longer than the request's arity. -/
theorem value_len (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (k : Nat) :
    (value a r k).length ≤ r.arity := by
  unfold value
  split
  · simp [PCPPQuerySupport.mask]
  · simp

/-! ## The entry predicate and the cost -/

/-- The cursor record of call `m` at the queried clause. -/
abbrev sigmaOf (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (ph : Phase) (m : Nat) : Option Sel :=
  selAt ph (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
    (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
    (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
    (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
    (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length m

/-- **The run's cost** (THR): front A + front B + back. `Rc`-free. -/
def selThrCost (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (ph : Phase) (L target cwid cw D b m : Nat) : Nat :=
  costA a r ci + 1 +
  (costB ph bits (literalIndex ((a.output r).clauses ci).left).val (literalIndex ((a.output r).clauses ci).right).val
      (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
      (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
      (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
      (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length + 1 +
    backThrCost (Tof coordinate ci) bits (literalIndex ((a.output r).clauses ci).left).val
      (literalIndex ((a.output r).clauses ci).right).val (sigmaOf a r ci coordinate ph m) cwid cw D r.arity L target
      (FactorLoop.factorsAt coordinate ph ci m).length (2 ^ (a.output r).clauseBits) b)

end
end NearCubicWires.SourceRequest.SelLocal

