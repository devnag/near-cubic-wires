import Proof.SourceAssembly.SourceRequestSelOrigCost
import Proof.SourceAssembly.SourceRequestSelWinLoop
import Proof.SourceAssembly.SourceFactorSelSysCost

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section
namespace NearCubicWires.SourceRequest.SelLoopCost
open PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.SourceRequest.FactorLoop (factorsAt factorsAt_le)
open NearCubicWires.SourceFactorSel

/-! ## Segments of a flat map -/

theorem seg_le_flat {α : Type} (f : α → List Bool) (l : List α) (x : α) (h : x ∈ l) :
    (f x).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with e | h'
    · subst e; omega
    · have := ih h'; omega

theorem mem_of_get {α : Type} (l : List α) (i : Nat) (x : α) (h : l[i]? = some x) : x ∈ l :=
  List.mem_of_getElem? h

/-! ## The constants -/

def slotE (a : DecompositionAlgorithm) : Nat :=
  max (max (SysCost.thrE a.degree) (SelOrigCost.thrOE a)) (max SysCost.symE 2)

def slotC (a : DecompositionAlgorithm) : Nat :=
  SysCost.thrC a.degree a.coefficient + SelOrigCost.thrOC a + SysCost.symC + 30004

def loopC (a : DecompositionAlgorithm) : Nat := 4 * slotC a + 1004

theorem one_le_slotE (a : DecompositionAlgorithm) : 2 ≤ slotE a := by
  unfold slotE; omega

theorem fit (x c C X : Nat) (hc : c ≤ C) (h : x ≤ c * X) : x ≤ C * X := h.trans (Nat.mul_le_mul_right X hc)

theorem addc (x y c X : Nat) (hX : 1 ≤ X) (h : x ≤ c * X) : x + y ≤ (c + y) * X := by
  rw [Nat.add_mul]
  have : y ≤ y * X := Nat.le_mul_of_pos_right y hX
  omega

theorem lift (S c e E x : Nat) (he : e ≤ E) (h : x ≤ c * (S + 1) ^ e) : x ≤ c * (S + 1) ^ E :=
  SelOrigCost.up S c e E x he h

theorem liftq (q S c e E x : Nat) (hq : q ≤ S) (he : e ≤ E) (h : x ≤ c * (q + 1) ^ e) : x ≤ c * (S + 1) ^ E :=
  h.trans (Nat.mul_le_mul_left c ((Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) he)))

section gen
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

theorem request_q (L target : Nat) (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    (monomialRequest L target mode atoms four).q = q := by
  cases mode <;> rfl

/-- The request's input is below `Yb`. -/
theorem input_le (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (S : Nat) (hY : WordsCost.Yb a (r, MB) ≤ S) :
    (r.input a).length ≤ S := by
  dsimp only [WordsCost.Yb] at hY
  omega

/-- A THR original factor's three words are segments of the request's. -/
theorem thr_words (a : DecompositionAlgorithm) (L target : Nat) (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) (MB : List Bool) (S : Nat)
    (hY : WordsCost.Yb a (monomialRequest L target false atoms four, MB) ≤ S)
    (c : NormalizedThresholdThresholdCircuit q) (hc : C10TotalDecode.Atom.threshold c ∈ atoms) :
    (thrWord c).length ≤ S ∧ (ThrOriginal.stream c).length ≤ S ∧
      (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c)).length ≤ S := by
  obtain ⟨_, hn, hs, _, ht, _⟩ := WordsCost.sizes_le a (monomialRequest L target false atoms four)
  have hi := input_le a _ MB S hY
  rw [native_eq] at hn
  rw [support_eq] at hs
  rw [top_eq] at ht
  have h1 := seg_le_flat (natSeg false) atoms _ hc
  have h2 := seg_le_flat (supSeg false) atoms _ hc
  have h3 := seg_le_flat (topSeg a false) atoms _ hc
  rw [List.length_append] at hn
  have e1 : (natSeg false (C10TotalDecode.Atom.threshold c : C10TotalDecode.Atom pcpp)).length = 2 * (thrWord c).length + 1 := by
    show (RepairOrdinary.frame (thrWord c)).length = _
    rw [frame_length]
  have e2 : supSeg false (C10TotalDecode.Atom.threshold c : C10TotalDecode.Atom pcpp) = ThrOriginal.stream c :=
    ThrOriginal.supSeg_threshold c
  have e3 : (topSeg a false (C10TotalDecode.Atom.threshold c : C10TotalDecode.Atom pcpp)).length =
      2 * (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c)).length + 1 := by
    show (RepairOrdinary.frame (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))).length = _
    rw [frame_length]
  rw [e2] at h2
  refine ⟨by omega, by omega, by omega⟩

/-- A SYM original factor's two words are segments of the request's. -/
theorem sym_words (a : DecompositionAlgorithm) (L target : Nat) (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) (MB : List Bool) (S : Nat)
    (hY : WordsCost.Yb a (monomialRequest L target true atoms four, MB) ≤ S)
    (c : NormalizedSymmetricThresholdCircuit q) (hc : C10TotalDecode.Atom.symmetric c ∈ atoms) :
    (symWord c).length ≤ S ∧ (SymOriginal.stream c).length ≤ S := by
  obtain ⟨_, hn, hs, _⟩ := WordsCost.sizes_le a (monomialRequest L target true atoms four)
  have hi := input_le a _ MB S hY
  rw [native_eq] at hn
  rw [support_eq] at hs
  have h1 := seg_le_flat (natSeg true) atoms _ hc
  have h2 := seg_le_flat (supSeg true) atoms _ hc
  rw [List.length_append] at hn
  have e1 : (natSeg true (C10TotalDecode.Atom.symmetric c : C10TotalDecode.Atom pcpp)).length = 2 * (symWord c).length + 1 := by
    show (RepairOrdinary.frame (symWord c)).length = _
    rw [frame_length]
  have e2 : supSeg true (C10TotalDecode.Atom.symmetric c : C10TotalDecode.Atom pcpp) = SymOriginal.stream c :=
    SymOriginal.supSeg_symmetric c
  rw [e2] at h2
  refine ⟨by omega, by omega⟩

/-- The request's `q` is below `Yb`. -/
theorem q_le (a : DecompositionAlgorithm) (L target : Nat) (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) (MB : List Bool) (S : Nat) (hY : WordsCost.Yb a (monomialRequest L target mode atoms four, MB) ≤ S) :
    q ≤ S := by
  obtain ⟨hq, _⟩ := WordsCost.sizes_le a (monomialRequest L target mode atoms four)
  rw [request_q] at hq
  have := input_le a _ MB S hY
  omega

/-- **One THR switch charge.** -/
theorem thrSlot_le (a : DecompositionAlgorithm) (Pw Ld L target : Nat) (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) (MB : List Bool) (S : Nat)
    (hY : WordsCost.Yb a (monomialRequest L target false atoms four, MB) ≤ S)
    (hP : Pw ≤ S) (hcw : ThrSwitch.codeWidth Ld ≤ S)
    (o : Option (C10TotalDecode.Atom pcpp)) (ho : ∀ x, o = some x → x ∈ atoms) :
    ThrSwitch.cost a Pw Ld o ≤ slotC a * (S + 1) ^ slotE a := by
  have hX : 1 ≤ (S + 1) ^ slotE a := Nat.one_le_pow _ _ (by omega)
  have hq := q_le a L target false atoms four MB S hY
  match o, ho with
  | none, _ =>
    show 0 + 2 + 2 ≤ _
    exact fit _ 4 _ _ (by unfold slotC; omega) (by omega)
  | some (.systematic idx), _ =>
    show ThrSystematic.cost a (pcpp.systematicSupport idx) + 2 ≤ _
    have h := liftq q S _ _ (slotE a) _ hq (by unfold slotE; omega)
      (SysCost.thrSys_cost_le a a.degree a.coefficient le_rfl le_rfl (pcpp.systematicSupport idx))
    exact fit _ _ _ _ (by unfold slotC; omega) (addc _ 2 _ _ hX h)
  | some (.threshold c), ho =>
    show ThrOriginal.cost a c Pw (ThrSwitch.codeBits Ld c) + 2 + 2 ≤ _
    obtain ⟨hN, hS, hT⟩ := thr_words a L target atoms four MB S hY c (ho _ rfl)
    have h := lift S _ _ (slotE a) _ (by unfold slotE; omega)
      (SelOrigCost.thrOrig_le a c Pw Ld S hq hP hcw hN hS hT)
    exact fit _ _ _ _ (by unfold slotC; omega) (addc _ 2 _ _ hX (addc _ 2 _ _ hX h))
  | some (.symmetric _), _ =>
    exact Nat.zero_le _

/-- **One SYM switch charge.** -/
theorem symSlot_le (a : DecompositionAlgorithm) (Pw Ld L target : Nat) (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) (MB : List Bool) (S : Nat)
    (hY : WordsCost.Yb a (monomialRequest L target true atoms four, MB) ≤ S)
    (hP : Pw ≤ S) (hcw : SymOriginal.symCodeWidth Ld ≤ S)
    (o : Option (C10TotalDecode.Atom pcpp)) (ho : ∀ x, o = some x → x ∈ atoms) :
    SymSwitch.cost Pw Ld o ≤ slotC a * (S + 1) ^ slotE a := by
  have hX : 1 ≤ (S + 1) ^ slotE a := Nat.one_le_pow _ _ (by omega)
  have hq := q_le a L target true atoms four MB S hY
  match o, ho with
  | none, _ =>
    show 0 + 2 + 2 ≤ _
    exact fit _ 4 _ _ (by unfold slotC; omega) (by omega)
  | some (.systematic idx), _ =>
    show SymSystematic.cost (pcpp.systematicSupport idx) + 2 ≤ _
    have h := liftq q S _ _ (slotE a) _ hq (by unfold slotE; omega) (SysCost.symSys_cost_le (pcpp.systematicSupport idx))
    exact fit _ _ _ _ (by unfold slotC; omega) (addc _ 2 _ _ hX h)
  | some (.symmetric c), ho =>
    show SymOriginal.cost c Pw (SymOriginal.symCodeBits Ld c) + 2 + 2 ≤ _
    obtain ⟨hN, hS⟩ := sym_words a L target atoms four MB S hY c (ho _ rfl)
    have h := lift S _ _ (slotE a) _ (by unfold slotE; omega) (SelOrigCost.symOrig_le c Pw Ld S hq hP hcw hN hS)
    exact fit _ _ _ _ (by unfold slotC; omega) (addc _ 2 _ _ hX (addc _ 2 _ _ hX h))
  | some (.threshold _), _ =>
    exact Nat.zero_le _

end gen

/-! ## The loop -/

theorem loop_le (sources : EightSources) (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output rq).clauseBits))
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (L target Pw W Ld : Nat) (mode : Bool) (m : Nat) (MB : List Bool) (S : Nat)
    (hY : WordsCost.Yb (decompositionOf sources) (requestAt coordinate ph ci L target mode m, MB) ≤ S)
    (hP : Pw ≤ S) (hcwT : ThrSwitch.codeWidth Ld ≤ S) (hcwS : SymOriginal.symCodeWidth Ld ≤ S)
    (hF : Fields.cost (header mode rq.arity L target (factorsAt coordinate ph ci m).length)
        (Fields.nSlots mode (factorsAt coordinate ph ci m)) (Fields.sSlots mode (factorsAt coordinate ph ci m))
        (Fields.tSlots (decompositionOf sources) mode (factorsAt coordinate ph ci m)) ≤ 1000 * (S + 1)) :
    SelWinCore.loopW sources a rq ci coordinate ph L target Pw W Ld mode m ≤
      loopC (decompositionOf sources) * (S + 1) ^ slotE (decompositionOf sources) := by
  have hX : 1 ≤ (S + 1) ^ slotE (decompositionOf sources) := Nat.one_le_pow _ _ (by omega)
  have hF' := hF.trans (Nat.mul_le_mul_left 1000 (SelOrigCost.lin_le S (slotE (decompositionOf sources))
    (by have := one_le_slotE (decompositionOf sources); omega)))
  have e : loopC (decompositionOf sources) * (S + 1) ^ slotE (decompositionOf sources) =
      4 * (slotC (decompositionOf sources) * (S + 1) ^ slotE (decompositionOf sources)) +
        1000 * (S + 1) ^ slotE (decompositionOf sources) + 4 * (S + 1) ^ slotE (decompositionOf sources) := by
    unfold loopC; ring
  rw [e]
  cases mode with
  | false =>
    have hs : ∀ i, ThrSwitch.cost (decompositionOf sources) Pw Ld (factorsAt coordinate ph ci m)[i]? ≤
        slotC (decompositionOf sources) * (S + 1) ^ slotE (decompositionOf sources) := fun i =>
      thrSlot_le (decompositionOf sources) Pw Ld L target (factorsAt coordinate ph ci m) (factorsAt_le coordinate ph ci m) MB S
        hY hP hcwT _ (fun x hx => mem_of_get _ i x hx)
    have h0 := hs 0
    have h1 := hs 1
    have h2 := hs 2
    have h3 := hs 3
    show ThrSwitch.cost (decompositionOf sources) Pw Ld (factorsAt coordinate ph ci m)[0]? + 1 +
        (ThrSwitch.cost (decompositionOf sources) Pw Ld (factorsAt coordinate ph ci m)[1]? + 1 +
        (ThrSwitch.cost (decompositionOf sources) Pw Ld (factorsAt coordinate ph ci m)[2]? + 1 +
        (ThrSwitch.cost (decompositionOf sources) Pw Ld (factorsAt coordinate ph ci m)[3]? + 1 +
          Fields.cost (header false rq.arity L target (factorsAt coordinate ph ci m).length)
            (Fields.nSlots false (factorsAt coordinate ph ci m)) (Fields.sSlots false (factorsAt coordinate ph ci m))
            (Fields.tSlots (decompositionOf sources) false (factorsAt coordinate ph ci m))))) ≤ _
    omega
  | true =>
    have hs : ∀ i, SymSwitch.cost (pcpp := a.output rq) Pw Ld (factorsAt coordinate ph ci m)[i]? ≤
        slotC (decompositionOf sources) * (S + 1) ^ slotE (decompositionOf sources) := fun i =>
      symSlot_le (decompositionOf sources) Pw Ld L target (factorsAt coordinate ph ci m) (factorsAt_le coordinate ph ci m) MB S
        hY hP hcwS _ (fun x hx => mem_of_get _ i x hx)
    have h0 := hs 0
    have h1 := hs 1
    have h2 := hs 2
    have h3 := hs 3
    show SymSwitch.cost (pcpp := a.output rq) Pw Ld (factorsAt coordinate ph ci m)[0]? + 1 +
        (SymSwitch.cost (pcpp := a.output rq) Pw Ld (factorsAt coordinate ph ci m)[1]? + 1 +
        (SymSwitch.cost (pcpp := a.output rq) Pw Ld (factorsAt coordinate ph ci m)[2]? + 1 +
        (SymSwitch.cost (pcpp := a.output rq) Pw Ld (factorsAt coordinate ph ci m)[3]? + 1 +
          Fields.cost (header true rq.arity L target (factorsAt coordinate ph ci m).length)
            (Fields.nSlots true (factorsAt coordinate ph ci m)) (Fields.sSlots true (factorsAt coordinate ph ci m))
            (Fields.tSlots (decompositionOf sources) true (factorsAt coordinate ph ci m))))) ≤ _
    omega

end NearCubicWires.SourceRequest.SelLoopCost
end

