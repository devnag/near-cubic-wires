import Proof.SourceAssembly.SourceRequestTermBridge

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace NearCubicWires.SourceRequest.TermCompose
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg

def aS (i : Fin 191) : Fin 1081 := ⟨i.val, by omega⟩
def bS (i : Fin 192) : Fin 1081 :=
  if i.val = 0 then ⟨189, by omega⟩ else if i.val = 189 then ⟨191, by omega⟩ else ⟨191 + i.val, by omega⟩
def cS (i : Fin 155) : Fin 1081 :=
  if i.val = 0 then ⟨381, by omega⟩ else if i.val = 151 then ⟨383, by omega⟩ else ⟨383 + i.val, by omega⟩
def dS (i : Fin 543) : Fin 1081 :=
  if i.val = 0 then ⟨422, by omega⟩ else if i.val = 534 then ⟨538, by omega⟩ else ⟨538 + i.val, by omega⟩

theorem aS_val (i : Fin 191) : (aS i).val = i.val := rfl
theorem bS_val (i : Fin 192) : (bS i).val = if i.val = 0 then 189 else if i.val = 189 then 191 else 191 + i.val := by
  unfold bS; split_ifs <;> rfl
theorem cS_val (i : Fin 155) : (cS i).val = if i.val = 0 then 381 else if i.val = 151 then 383 else 383 + i.val := by
  unfold cS; split_ifs <;> rfl
theorem dS_val (i : Fin 543) : (dS i).val = if i.val = 0 then 422 else if i.val = 534 then 538 else 538 + i.val := by
  unfold dS; split_ifs <;> rfl

theorem aS_inj : Function.Injective aS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; rwa [aS_val, aS_val] at this)
theorem bS_inj : Function.Injective bS := by
  intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; rw [bS_val, bS_val] at hv
  have hi := i.isLt; have hj := j.isLt; split_ifs at hv <;> omega
theorem cS_inj : Function.Injective cS := by
  intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; rw [cS_val, cS_val] at hv
  have hi := i.isLt; have hj := j.isLt; split_ifs at hv <;> omega
theorem dS_inj : Function.Injective dS := by
  intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; rw [dS_val, dS_val] at hv
  have hi := i.isLt; have hj := j.isLt; split_ifs at hv <;> omega

theorem off {t : Nat} (slots : Fin t → Fin 1081) (A : Fin 1081 → List Bool) (T : Fin t → List Bool) (x : Fin 1081)
    (h : ∀ j, (slots j).val ≠ x.val) : install slots A T x = A x :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

open RepairSource.VerifierDecoding in
/-- The reader's exact entry: witness, the two counters, the two widths, the four segments' `[false]` tapes. -/
def entry (bits : List Bool) (j i cwid cw : Nat) : Fin 1081 → List Bool := fun x =>
  if x.val = 0 then frame bits else if x.val = 188 then CompareMachine.word j
  else if x.val = 191 then CompareMachine.word i else if x.val = 383 then List.replicate cwid true
  else if x.val = 538 then List.replicate cw true
  else if x.val = 1 ∨ x.val = 192 ∨ x.val = 384 ∨ x.val = 539 then [false] else []

noncomputable def machine :=
  Composition.machine
    (Composition.machine
      (Composition.machine (RecoveryFocus.machine aS machineA) (RecoveryFocus.machine bS TermSegB.machineB))
      (RecoveryFocus.machine cS TermSegC.machine))
    (RecoveryFocus.machine dS TermCoef.machine)

theorem entry_nil (bits : List Bool) (j i cwid cw : Nat) (x : Fin 1081) (h0 : x.val ≠ 0) (h188 : x.val ≠ 188)
    (h191 : x.val ≠ 191) (h383 : x.val ≠ 383) (h538 : x.val ≠ 538) (h1 : x.val ≠ 1) (h192 : x.val ≠ 192)
    (h384 : x.val ≠ 384) (h539 : x.val ≠ 539) : entry bits j i cwid cw x = [] := by
  unfold entry
  rw [if_neg h0, if_neg h188, if_neg h191, if_neg h383, if_neg h538, if_neg (by omega)]

theorem entry_false (bits : List Bool) (j i cwid cw : Nat) (x : Fin 1081)
    (h : x.val = 1 ∨ x.val = 192 ∨ x.val = 384 ∨ x.val = 539) : entry bits j i cwid cw x = [false] := by
  unfold entry
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

/-- The words the reader reaches (total forms; equal to the indexed ones under the bridge's bounds). -/
noncomputable def cWord (bits : List Bool) (j : Nat) : List Bool :=
  SignedSortKey.binary bits.length ((sums bits).getD j 0)
noncomputable def tWord (bits : List Bool) (j i : Nat) : List Bool :=
  SignedSortKey.binary (cWord bits j).length ((TermSegB.terms (cWord bits j)).getD i 0)

noncomputable def readerCost (bits : List Bool) (j i cwid cw : Nat) : Nat :=
  costA bits.length j + 1 + TermSegB.costB (cWord bits j).length i + 1 +
    TermSegC.cost (tWord bits j i).length cwid + 1 +
    TermCoef.cost (CloseoutWitness.PairHeader.codeWord (tWord bits j i) 0) cw

open RepairSource.VerifierDecoding TermReader in

theorem reader_exact (bits : List Bool) (j i cwid cw : Nat) (ts : List (ℚ × Nat)) (h : rawTerms bits j = some ts)
    (hi : i < ts.length) :
    ∃ X : Fin 1081 → List Bool,
      Step machine (readerCost bits j i cwid cw) (fun _ => 0) (entry bits j i cwid cw) (fun _ => 0) X ∧
      X 0 = frame bits ∧ X 188 = CompareMachine.word j ∧ X 191 = CompareMachine.word i ∧
      X 383 = List.replicate cwid true ∧ X 538 = List.replicate cw true ∧
      X 370 = List.replicate ts.length true ∧
      X 535 = frame (SignedSortKey.binary cwid ts[i].2) ∧
      X 1079 = CloseoutRowsEstimatorCoefficients.Product.record cw ts[i].1 := by
  obtain ⟨hj, hi', hlen, hcode, hcoef⟩ := TermBridge.chain bits j i cwid cw ts h hi
  -- segment A
  obtain ⟨XA, sA, xa0, xa188, xa189, _⟩ := segA_run bits j hj
  have hEA : ∀ k, entry bits j i cwid cw (aS k) = entryA bits j k := by
    intro k
    have hk := k.isLt
    unfold entry entryA
    simp only [aS_val]
    split_ifs <;> first | rfl | omega
  have dA := dock sA aS aS_inj (fun _ => 0) _ (fun _ => rfl) hEA
  -- segment B
  obtain ⟨XB, sB, xb0, xb189, xb190, xb179⟩ :=
    TermSegB.segB_run (SignedSortKey.binary bits.length (sums bits)[j]) i hi'
  have hEB : ∀ k, install aS (entry bits j i cwid cw) XA (bS k) =
      TermSegB.entryB (SignedSortKey.binary bits.length (sums bits)[j]) i k := by
    intro k
    have hk := k.isLt
    by_cases h0 : k.val = 0
    · have e : bS k = aS 189 := Fin.ext (by rw [bS_val, if_pos h0]; rfl)
      rw [e, install_slot _ aS_inj, xa189]
      unfold TermSegB.entryB; rw [if_pos h0]
    · rw [off _ _ _ _ (by intro m; rw [aS_val, bS_val]; have := m.isLt; split_ifs <;> omega)]
      have hv := bS_val k
      rw [if_neg h0] at hv
      unfold TermSegB.entryB
      rw [if_neg h0]
      by_cases h1 : k.val = 1
      · rw [if_pos h1, entry_false _ _ _ _ _ _ (by rw [hv, if_neg (by omega)]; omega)]
      · rw [if_neg h1]
        by_cases h189 : k.val = 189
        · rw [if_pos h189]
          unfold entry
          rw [hv, if_pos h189]
          simp
        · rw [if_neg h189]
          have hw := hv
          rw [if_neg h189] at hw
          exact entry_nil _ _ _ _ _ _ (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega)
            (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega)
            (by rw [hw]; omega) (by rw [hw]; omega)
  have dB := dock sB bS bS_inj (fun _ => 0) _ (fun _ => rfl) hEB
  -- segment C
  let c := SignedSortKey.binary bits.length (sums bits)[j]
  obtain ⟨XC, sC, xc0, xc151, xc152, xc39⟩ :=
    TermSegC.circuit_run (SignedSortKey.binary c.length (TermSegB.terms c)[i]) cwid
  have hEC : ∀ k, install bS (install aS (entry bits j i cwid cw) XA) XB (cS k) =
      TermSegC.entry (SignedSortKey.binary c.length (TermSegB.terms c)[i]) cwid k := by
    intro k
    have hk := k.isLt
    by_cases h0 : k.val = 0
    · have e : cS k = bS 190 := Fin.ext (by rw [cS_val, bS_val, if_pos h0]; rfl)
      rw [e, install_slot _ bS_inj, xb190]
      unfold TermSegC.entry; rw [if_pos h0]
    · rw [off _ _ _ _ (by intro m; rw [bS_val, cS_val]; have := m.isLt; split_ifs <;> omega),
        off _ _ _ _ (by intro m; rw [aS_val, cS_val]; have := m.isLt; split_ifs <;> omega)]
      have hv := cS_val k
      rw [if_neg h0] at hv
      unfold TermSegC.entry
      rw [if_neg h0]
      by_cases h1 : k.val = 1
      · rw [if_pos h1, entry_false _ _ _ _ _ _ (by rw [hv, if_neg (by omega)]; omega)]
      · rw [if_neg h1]
        by_cases h151 : k.val = 151
        · rw [if_pos h151]
          unfold entry
          rw [hv, if_pos h151]
          simp
        · rw [if_neg h151]
          have hw := hv
          rw [if_neg h151] at hw
          exact entry_nil _ _ _ _ _ _ (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega)
            (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega)
            (by rw [hw]; omega) (by rw [hw]; omega)
  have dC := dock sC cS cS_inj (fun _ => 0) _ (fun _ => rfl) hEC
  -- the coefficient half
  obtain ⟨XD, sD, xd0, xd534, xd541⟩ :=
    TermCoef.coef_run (CloseoutWitness.PairHeader.codeWord (SignedSortKey.binary c.length (TermSegB.terms c)[i]) 0) cw
  have hED : ∀ k, install cS (install bS (install aS (entry bits j i cwid cw) XA) XB) XC (dS k) =
      TermCoef.entry (CloseoutWitness.PairHeader.codeWord (SignedSortKey.binary c.length (TermSegB.terms c)[i]) 0)
        cw k := by
    intro k
    have hk := k.isLt
    by_cases h0 : k.val = 0
    · have e : dS k = cS 39 := Fin.ext (by rw [dS_val, cS_val, if_pos h0]; rfl)
      rw [e, install_slot _ cS_inj, xc39]
      unfold TermCoef.entry; rw [if_pos h0]
    · rw [off _ _ _ _ (by intro m; rw [cS_val, dS_val]; have := m.isLt; split_ifs <;> omega),
        off _ _ _ _ (by intro m; rw [bS_val, dS_val]; have := m.isLt; split_ifs <;> omega),
        off _ _ _ _ (by intro m; rw [aS_val, dS_val]; have := m.isLt; split_ifs <;> omega)]
      have hv := dS_val k
      rw [if_neg h0] at hv
      unfold TermCoef.entry
      rw [if_neg h0]
      by_cases h1 : k.val = 1
      · rw [if_pos h1, entry_false _ _ _ _ _ _ (by rw [hv, if_neg (by omega)]; omega)]
      · rw [if_neg h1]
        by_cases h534 : k.val = 534
        · rw [if_pos h534]
          unfold entry
          rw [hv, if_pos h534]
          simp
        · rw [if_neg h534]
          have hw := hv
          rw [if_neg h534] at hw
          exact entry_nil _ _ _ _ _ _ (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega)
            (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega)
            (by rw [hw]; omega) (by rw [hw]; omega)
  have dD := dock sD dS dS_inj (fun _ => 0) _ (fun _ => rfl) hED
  have hcw : cWord bits j = SignedSortKey.binary bits.length (sums bits)[j] := by
    unfold cWord; rw [List.getD_eq_getElem _ _ hj]
  have htw : tWord bits j i = SignedSortKey.binary c.length (TermSegB.terms c)[i] := by
    unfold tWord; simp only [hcw]; rw [List.getD_eq_getElem _ _ hi']
  have whole := ((dA.seq dB).seq dC).seq dD
  have ecost : costA bits.length j + 1 + TermSegB.costB c.length i + 1 +
      TermSegC.cost (SignedSortKey.binary c.length (TermSegB.terms c)[i]).length cwid + 1 +
      TermCoef.cost (CloseoutWitness.PairHeader.codeWord (SignedSortKey.binary c.length (TermSegB.terms c)[i]) 0) cw =
      readerCost bits j i cwid cw := by
    unfold readerCost; rw [hcw, htw]
  rw [ecost] at whole
  refine ⟨_, whole, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [off _ _ _ _ (by intro m; rw [dS_val]; split_ifs <;> simp <;> omega),
      off _ _ _ _ (by intro m; rw [cS_val]; split_ifs <;> simp <;> omega),
      off _ _ _ _ (by intro m; rw [bS_val]; split_ifs <;> simp <;> omega)]
    show install aS _ _ (aS 0) = _
    rw [install_slot _ aS_inj, xa0]
  · rw [off _ _ _ _ (by intro m; rw [dS_val]; split_ifs <;> simp <;> omega),
      off _ _ _ _ (by intro m; rw [cS_val]; split_ifs <;> simp <;> omega),
      off _ _ _ _ (by intro m; rw [bS_val]; split_ifs <;> simp <;> omega)]
    show install aS _ _ (aS 188) = _
    rw [install_slot _ aS_inj, xa188]
  · rw [off _ _ _ _ (by intro m; rw [dS_val]; split_ifs <;> simp <;> omega),
      off _ _ _ _ (by intro m; rw [cS_val]; split_ifs <;> simp <;> omega)]
    show install bS _ _ (bS 189) = _
    rw [install_slot _ bS_inj, xb189]
  · rw [off _ _ _ _ (by intro m; rw [dS_val]; split_ifs <;> simp <;> omega)]
    show install cS _ _ (cS 151) = _
    rw [install_slot _ cS_inj, xc151]
  · show install dS _ _ (dS 534) = _
    rw [install_slot _ dS_inj, xd534]
  · rw [off _ _ _ _ (by intro m; rw [dS_val]; split_ifs <;> simp <;> omega),
      off _ _ _ _ (by intro m; rw [cS_val]; split_ifs <;> simp <;> omega)]
    show install bS _ _ (bS 179) = _
    rw [install_slot _ bS_inj, xb179, hlen]
  · rw [off _ _ _ _ (by intro m; rw [dS_val]; split_ifs <;> simp <;> omega)]
    show install cS _ _ (cS 152) = _
    rw [install_slot _ cS_inj, xc152, hcode]
  · show install dS _ _ (dS 541) = _
    rw [install_slot _ dS_inj, xd541, hcoef]

end NearCubicWires.SourceRequest.TermCompose

