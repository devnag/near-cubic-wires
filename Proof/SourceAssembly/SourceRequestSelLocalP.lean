import Proof.SourceAssembly.SourceRequestSelLocalK
import Proof.SourceAssembly.SourceRequestSelFrontP

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
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

/-- **FactorSelection on the local universe, THR mode.** From the local entry bank (heads all `0`), at call `m ≤ N`: `word N` on
`nT = 33` (head `0`); every fixed port `< 100` other than `33..36` unchanged (head `0`); the region entries of monomial `m`
(heads `0`); the `coefT = 34..36` heads `0` at every `m ≤ N`, and their words for `m < N`. Scratch = the fixed ports `≥ 100`. -/
theorem sel_thr_localP (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (hread : CoordReads false coordinate bits) (ph : Phase)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length)
    (L target cwid cw D b Rc c QK : Nat) (pw : List Bool)
    
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
    (hwinA : litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 1 ≤ Rc)
    (hiL : index ((a.output r).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output r).clauses ci).right + 3 ≤ Rc)
    -- front B (count readers, cursor)
    (hcL : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length ≤ Rc)
    -- back (slots, header, coefficient words)
    (hcwid : cwid = ThrSwitch.codeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex ((a.output r).clauses ci).left).val ∨
      jj = (literalIndex ((a.output r).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : r.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : SourceFactorSel.HdrBlock.Fits false r.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D
      Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (V : Nat) (hV4 : 4 ≤ V)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < V ∧ mo.coefficient.den < V)
    (hbigR : SourceFactorSel.CoefR.coefBigR V (2 ^ (a.output r).clauseBits) b (cw + rhoW) ≤ Rc)
    (A : Fin (NF + (19 + 4 * tT da)) → List Bool)
    (hin : LocalInK (tT da) false A
      (fun j => PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
        (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j)
      bits m r.arity Pw W Ld L target cwid cw D (2 ^ (a.output r).clauseBits) b Rc QK) :
    ∃ (H' : Fin (NF + (19 + 4 * tT da)) → Nat) (A' : Fin (NF + (19 + 4 * tT da)) → List Bool),
      Step (selThrM ph da) (selThrCost a r ci coordinate bits ph L target cwid cw D b m) (fun _ => 0) A H' A' ∧
      H' (up 33) = 0 ∧
      A' (up 33) = ZeroPadding.pad Rc (CompareMachine.word (FactorLoop.monomials coordinate ph ci).length) ∧
      (∀ k (hk : k < 100), k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 →
        A' (up ⟨k, by unfold NF; omega⟩) = A (up ⟨k, by unfold NF; omega⟩) ∧ H' (up ⟨k, by unfold NF; omega⟩) = 0) ∧
      (∀ x, H' (rgP (PT (pcpp := a.output r) da Pw W Ld) x) = 0) ∧
      (∀ x, A' (rgP (PT (pcpp := a.output r) da Pw W Ld) x) = FactorLoop.entry (PT (pcpp := a.output r) da Pw W Ld)
        (header false r.arity L target (FactorLoop.factorsAt coordinate ph ci m).length)
        (fun k => (PT (pcpp := a.output r) da Pw W Ld).Desc (FactorLoop.factorsAt coordinate ph ci m)[k.val]?) Rc x) ∧
      (∀ i : Fin 3, H' (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = 0) ∧
      (∀ hm' : m < (FactorLoop.monomials coordinate ph ci).length, ∀ i : Fin 3,
        A' (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = ZeroPadding.pad Rc (RepairOrdinary.frame
          (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
            (CloseoutFinalC10SupplierCalls.coefficientEstimate ((FactorLoop.monomials coordinate ph ci)[m]).coefficient)
            0 0 ⟨i.val, by omega⟩))) := by
  -- front A, on the swapped view
  obtain ⟨Aa, sa, a129, a130, a141, a142, a185, a189, a103, a104, a200, a201, aKeep, -⟩ :=
    front_aP a r ci Rc pw (fun z => A (us z)) hc hwinA hQR hiL hiR
      (fun j => by
        have := j.isLt
        show A (up (sw ⟨j.val, _⟩)) = _
        rw [sw_ne _ (by show j.val ≠ 36; omega) (by show j.val ≠ 39; omega)]
        exact hin.cache j)
      (fun p hp => by
        show A (up (sw p)) = _
        by_cases h39 : p.val = 39
        · have e : sw p = ⟨36, by decide⟩ := Fin.ext (by show swv p.val = 36; rw [h39]; rfl)
          rw [e]; exact hin.blank 36 _ (by omega) (by omega)
        · rw [sw_ne p (by omega) h39]; exact hin.blank p.val p.isLt (by omega) h39)
  have sa' : Step (RecoveryFocus.machine (us (t := tT da)) pA.2) (costA a r ci) (fun _ => 0) A (fun _ => 0)
      (install us A Aa) :=
    ((frontA_packed _ _ _ _ _ sa).dock us us_inj (fun _ => 0) A (fun _ => rfl) (fun _ => rfl)).congr
      (dockH_existing us (fun _ => 0) (fun _ => 0) (fun _ => rfl)) rfl
  have hA1 : ∀ z : Fin NF, install us A Aa (up z) = Aa (sw z) := by
    intro z; rw [up_us z]; exact install_slot us us_inj A Aa (sw z)
  have kA1 : ∀ z : Fin NF, z.val < 100 ∨ 202 ≤ z.val → install us A Aa (up z) = A (up z) := by
    intro z hz
    rw [hA1 z, aKeep (sw z) (swv_keep z.val hz)]
    show A (up (sw (sw z))) = _
    rw [sw_sw]
  have oA1 : ∀ z : Fin NF, z.val ≠ 36 → z.val ≠ 39 → install us A Aa (up z) = Aa z := by
    intro z h1 h2; rw [hA1 z, sw_ne z h1 h2]
  have rA1 : ∀ x, install us A Aa (Fin.natAdd NF x) = A (Fin.natAdd NF x) := by
    intro x
    apply install_other
    intro j e
    have hv := congrArg Fin.val e
    simp only [us, up_val, Fin.val_natAdd] at hv
    have := (sw j).isLt
    omega
  -- front B, docked by `up`
  obtain ⟨Hb, Ab, sb, b33, bcur, bcurH, bH33, bKeep⟩ :=
    front_b ph a r ci false coordinate bits hread m Rc (fun z => install us A Aa (up z)) hm hcL hcR hbig
      ((kA1 19 (by decide)).trans hin.wit) ((kA1 20 (by decide)).trans hin.cur)
      ((oA1 185 (by decide) (by decide)).trans a185) ((oA1 189 (by decide) (by decide)).trans a189)
      ((oA1 130 (by decide) (by decide)).trans a130) ((oA1 142 (by decide) (by decide)).trans a142)
      ((oA1 200 (by decide) (by decide)).trans a200) ((oA1 201 (by decide) (by decide)).trans a201)
      ((kA1 33 (by decide)).trans (hin.blank 33 _ (by omega) (by omega)))
      ((kA1 40 (by decide)).trans (hin.blank 40 _ (by omega) (by omega)))
      ((kA1 41 (by decide)).trans (hin.blank 41 _ (by omega) (by omega)))
      (fun z hz => (kA1 z (Or.inr hz)).trans (hin.blank z.val z.isLt (by omega) (by omega)))
  have sb' : Step (RecoveryFocus.machine (up (t := tT da)) (pB ph).2) _ (fun _ => 0) (install us A Aa)
      (dockH up (fun _ => 0) Hb) (install up (install us A Aa) Ab) :=
    (frontB_packed ph _ _ _ _ _ sb).dock up up_inj (fun _ => 0) (install us A Aa) (fun _ => rfl) (fun _ => rfl)
  -- the bank after the front
  have hA2 : ∀ z : Fin NF, install up (install us A Aa) Ab (up z) = Ab z := fun z => install_slot up up_inj _ _ z
  have hH2 : ∀ z : Fin NF, dockH up (fun _ => 0) Hb (up (t := tT da) z) = Hb z := fun z => dockH_slot up up_inj _ _ z
  have rA2 : ∀ x, install up (install us A Aa) Ab (Fin.natAdd NF x) = A (Fin.natAdd NF x) := by
    intro x
    rw [install_other up _ Ab _ (fun j e => by
      have hv := congrArg Fin.val e
      simp only [up_val, Fin.val_natAdd] at hv
      have := j.isLt
      omega)]
    exact rA1 x
  have low : ∀ z : Fin NF, z.val < 100 → z.val ≠ 33 →
      install up (install us A Aa) Ab (up z) = A (up z) := by
    intro z hz h33
    rw [hA2 z, (bKeep z (Or.inl (by omega)) (fun e => h33 (by rw [e]; rfl))).1]
    exact kA1 z (Or.inl hz)
  have mid : ∀ z : Fin NF, z.val < 300 → z.val ≠ 33 → z.val ≠ 36 → z.val ≠ 39 →
      install up (install us A Aa) Ab (up z) = Aa z := by
    intro z hz h33 h36 h39
    rw [hA2 z, (bKeep z (Or.inl hz) (fun e => h33 (by rw [e]; rfl))).1]
    exact oA1 z h36 h39
  have high : ∀ z : Fin NF, 1400 ≤ z.val → install up (install us A Aa) Ab (up z) = A (up z) := by
    intro z hz
    rw [hA2 z, (bKeep z (Or.inr hz) (fun e => by rw [e] at hz; revert hz; decide)).1]
    exact kA1 z (Or.inr (by omega))
  have headsF : ∀ z : Fin NF, ¬ (300 ≤ z.val ∧ z.val < 1400) → dockH up (fun _ => 0) Hb (up (t := tT da) z) = 0 := by
    intro z hz
    rw [hH2 z]
    by_cases h33 : z = 33
    · rw [h33]; exact bH33
    · exact (bKeep z (by omega) h33).2
  -- the back's entry
  have hback : BackInK (PT (pcpp := a.output r) da Pw W Ld).t false (install up (install us A Aa) Ab)
      (dockH up (fun _ => 0) Hb) (sigmaOf a r ci coordinate ph m) ph bits r.arity Pw W Ld L target cwid cw D
      (2 ^ (a.output r).clauseBits) b (literalIndex ((a.output r).clauses ci).left).val
      (literalIndex ((a.output r).clauses ci).right).val Rc
      (value a r (literalIndex ((a.output r).clauses ci).left).val)
      (value a r (literalIndex ((a.output r).clauses ci).right).val) QK := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact cursorOut_of_eq (fun j => hA2 _) bcur
    · exact (low 19 (by decide) (by decide)).trans hin.wit
    · exact (low 21 (by decide) (by decide)).trans hin.tpl
    · exact (low 22 (by decide) (by decide)).trans hin.uP
    · exact (low 23 (by decide) (by decide)).trans hin.uW
    · exact (low 24 (by decide) (by decide)).trans hin.uL
    · intro i
      have := i.isLt
      exact (low _ (by show 25 + i.val < 100; omega) (by show 25 + i.val ≠ 33; omega)).trans (hin.hdr i)
    · exact (low 29 (by decide) (by decide)).trans hin.ucwid
    · exact (low 30 (by decide) (by decide)).trans hin.ucw
    · exact (low 31 (by decide) (by decide)).trans hin.uD
    · exact (low 32 (by decide) (by decide)).trans hin.uK
    · exact (low 39 (by decide) (by decide)).trans hin.ub
    · exact (mid 129 (by decide) (by decide) (by decide) (by decide)).trans a129
    · exact (mid 141 (by decide) (by decide) (by decide) (by decide)).trans a141
    · exact (mid 103 (by decide) (by decide) (by decide) (by decide)).trans a103
    · exact (mid 104 (by decide) (by decide) (by decide) (by decide)).trans a104
    · intro i
      have := i.isLt
      exact (low _ (by show 34 + i.val < 100; omega) (by show 34 + i.val ≠ 33; omega)).trans
        (hin.blank _ _ (by omega) (by omega))
    · exact ⟨(low 42 (by decide) (by decide)).trans (hin.blank 42 _ (by omega) (by omega)),
        (low 43 (by decide) (by decide)).trans (hin.blank 43 _ (by omega) (by omega)),
        (low 44 (by decide) (by decide)).trans (hin.blank 44 _ (by omega) (by omega))⟩
    · intro k hk h1400
      exact (high ⟨k, hk⟩ h1400).trans (hin.blank k hk (by omega) (by omega))
    · intro x
      exact (rA2 x).trans (hin.region x)
    · intro z hz
      by_cases hzl : z.val < NF
      · have e : z = up ⟨z.val, hzl⟩ := Fin.ext rfl
        rw [e]
        exact headsF _ hz
      · exact dockH_other up _ Hb z (fun j e => by
          have hv := congrArg Fin.val e
          rw [up_val] at hv
          have := j.isLt
          omega)
    · intro j
      exact (hH2 _).trans (bcurH j)
  -- the back
  obtain ⟨H3, A3, s3, rH, rA, cH, cA, keep3⟩ := back_thrK (pcpp := a.output r) da Pw W Ld coordinate bits hread ph ci
    (Tof coordinate ci) (eOf (a.output r) ci) rfl rfl
    (fun h => atomAt_sys (a.output r) _ h) (fun h => atomAt_sys (a.output r) _ h) m hm L target cwid cw D b Rc c QK
    (value a r (literalIndex ((a.output r).clauses ci).left).val)
    (value a r (literalIndex ((a.output r).clauses ci).right).val) hcwid h2cw
    (fun h => SourceFactorSel.SlotRead.value_eq_bitmap a r _ h)
    (fun h => SourceFactorSel.SlotRead.value_eq_bitmap a r _ h)
    ⟨(value_len a r _).trans (by omega), (value_len a r _).trans (by omega)⟩
    hwinR hqD hPD hWD hLD hDR hDC hHfit hcw1 hcoef V hV4 hcoefV hbigR (sigmaOf a r ci coordinate ph m) rfl _ _ hback
  have st := sa'.seq (sb'.seq s3)
  refine ⟨H3, A3, st, ?_, ?_, ?_, rH, rA, cH, cA⟩
  · exact (keep3 33 (by decide) (by decide) (by decide) (by decide)).2.trans (headsF 33 (by decide))
  · exact (keep3 33 (by decide) (by decide) (by decide) (by decide)).1.trans ((hA2 33).trans b33)
  · intro k hk h33 h34 h35 h36
    obtain ⟨k1, k2⟩ := keep3 k (by omega) h34 h35 h36
    refine ⟨k1.trans (low ⟨k, by unfold NF; omega⟩ hk h33), k2.trans (headsF _ (by show ¬ (300 ≤ k ∧ k < 1400); omega))⟩

/-- **`Item4.SelRun` for THR FactorSelection, docked by `g`.** -/
theorem selRun_thrP {V : Nat} (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (hread : CoordReads false coordinate bits) (ph : Phase)
    (L target cwid cw D b Rc c qCap QK : Nat) (pw : List Bool)
    (g : Fin (NF + (19 + 4 * tT da)) → Fin V) (hg : Function.Injective g)
    (qTape nT : Fin V) (coefT : Fin 3 → Fin V) (hnT : g (up 33) = nT)
    (hcT : ∀ i : Fin 3, g (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = coefT i)
    (In : Nat → (Fin V → Nat) → (Fin V → List Bool) → Prop)
    (hIn : ∀ m H A, In m H A → (∀ z, H (g z) = 0) ∧
      LocalInK (tT da) false (fun z => A (g z))
        (fun j => PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
          (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j)
        bits m r.arity Pw W Ld L target cwid cw D (2 ^ (a.output r).clauseBits) b Rc QK)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
    (hwinA : litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 1 ≤ Rc)
    (hiL : index ((a.output r).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output r).clauses ci).right + 3 ≤ Rc)
    (hcL : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length ≤ Rc)
    (hcwid : cwid = ThrSwitch.codeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex ((a.output r).clauses ci).left).val ∨
      jj = (literalIndex ((a.output r).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : r.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : ∀ m, m ≤ (FactorLoop.monomials coordinate ph ci).length →
      SourceFactorSel.HdrBlock.Fits false r.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (Vb : Nat) (hV4 : 4 ≤ Vb)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hbigR : SourceFactorSel.CoefR.coefBigR Vb (2 ^ (a.output r).clauseBits) b (cw + rhoW) ≤ Rc) :
    SourceFactorSel.Item4.SelRun (RecoveryFocus.machine g (selThrM ph da))
      (fun m => selThrCost a r ci coordinate bits ph L target cwid cw D b m)
      (PT (pcpp := a.output r) da Pw W Ld) coordinate ph ci L target Rc b qCap
      (fun x => g (rgP (PT (pcpp := a.output r) da Pw W Ld) x)) qTape nT coefT
      (fun x => ∃ z : Fin NF, 100 ≤ z.val ∧ g (up z) = x) In := by
  intro m hm H A hin _ _
  obtain ⟨hH0, hL⟩ := hIn m H A hin
  obtain ⟨H', A', st, h33, a33, keep, rH, rA, cH, cA⟩ := sel_thr_localP da Pw W Ld a r ci coordinate bits hread ph m hm
    L target cwid cw D b Rc c QK pw hc hwinA hQR hiL hiR hcL hcR hbig hcwid h2cw hwinR hqD hPD hWD hLD hDR hDC (hHfit m hm)
    hcw1 hcoef Vb hV4 hcoefV hbigR (fun z => A (g z)) hL
  have st' := st.dock g hg H A (fun z => hH0 z) (fun z => rfl)
  refine ⟨dockH g H H', install g A A', st', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hnT, dockH_slot g hg]; exact h33
  · rw [← hnT, install_slot g hg]; exact a33
  · intro x hreg hn hc' hscr
    by_cases hx : ∃ z, g z = x
    · obtain ⟨z, rfl⟩ := hx
      rw [install_slot g hg, dockH_slot g hg]
      by_cases hz : z.val < NF
      · have ez : z = up ⟨z.val, hz⟩ := Fin.ext rfl
        have hk100 : z.val < 100 := by
          by_contra h
          exact hscr ⟨⟨z.val, hz⟩, Nat.le_of_not_lt h, by rw [← ez]⟩
        have hk33 : z.val ≠ 33 := by
          intro e
          apply hn
          rw [← hnT]
          exact congrArg g (Fin.ext (by rw [up_val]; exact e))
        have hk3 : ∀ i : Fin 3, z.val ≠ 34 + i.val := by
          intro i e
          apply hc' i
          rw [← hcT i]
          exact congrArg g (Fin.ext (by rw [up_val]; exact e.symm))
        have h34 := hk3 0
        have h35 := hk3 1
        have h36 := hk3 2
        obtain ⟨a1, h1⟩ := keep z.val hk100 hk33 h34 h35 h36
        rw [ez]
        exact ⟨a1, h1.trans (hH0 _).symm⟩
      · exfalso
        have hPt : (PT (pcpp := a.output r) da Pw W Ld).t = tT da := rfl
        apply hreg ⟨z.val - NF, by have := z.isLt; rw [hPt]; unfold NF at *; omega⟩
        exact congrArg g (Fin.ext (show NF + (z.val - NF) = z.val by omega))
    · exact ⟨install_other g A A' x (fun z e => hx ⟨z, e⟩), dockH_other g H H' x (fun z e => hx ⟨z, e⟩)⟩
  · intro i; exact (dockH_slot g hg _ _ _).trans (rH i)
  · intro i; exact (install_slot g hg _ _ _).trans (rA i)
  · intro i; rw [← hcT i, dockH_slot g hg]; exact cH i
  · intro hm' i; rw [← hcT i, install_slot g hg]; exact cA hm' i

/-- **FactorSelection on the local universe, SYM mode.** From the local entry bank (heads all `0`), at call `m ≤ N`: `word N` on
`nT = 33` (head `0`); every fixed port `< 100` other than `33..36` unchanged (head `0`); the region entries of monomial `m`
(heads `0`); the `coefT = 34..36` heads `0` at every `m ≤ N`, and their words for `m < N`. Scratch = the fixed ports `≥ 100`. -/
theorem sel_sym_localP (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (hread : CoordReads true coordinate bits) (ph : Phase)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length)
    (L target cwid cw D b Rc c QK : Nat) (pw : List Bool)
    
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
    (hwinA : litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 1 ≤ Rc)
    (hiL : index ((a.output r).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output r).clauses ci).right + 3 ≤ Rc)
    -- front B (count readers, cursor)
    (hcL : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length ≤ Rc)
    -- back (slots, header, coefficient words)
    (hcwid : cwid = SymOriginal.symCodeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex ((a.output r).clauses ci).left).val ∨
      jj = (literalIndex ((a.output r).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : r.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : SourceFactorSel.HdrBlock.Fits true r.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D
      Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (V : Nat) (hV4 : 4 ≤ V)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < V ∧ mo.coefficient.den < V)
    (hbigR : SourceFactorSel.CoefR.coefBigR V (2 ^ (a.output r).clauseBits) b (cw + rhoW) ≤ Rc)
    (A : Fin (NF + (19 + 4 * tS)) → List Bool)
    (hin : LocalInK tS true A
      (fun j => PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
        (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j)
      bits m r.arity Pw W Ld L target cwid cw D (2 ^ (a.output r).clauseBits) b Rc QK) :
    ∃ (H' : Fin (NF + (19 + 4 * tS)) → Nat) (A' : Fin (NF + (19 + 4 * tS)) → List Bool),
      Step (selSymM ph) (selSymCost a r ci coordinate bits ph L target cwid cw D b m) (fun _ => 0) A H' A' ∧
      H' (up 33) = 0 ∧
      A' (up 33) = ZeroPadding.pad Rc (CompareMachine.word (FactorLoop.monomials coordinate ph ci).length) ∧
      (∀ k (hk : k < 100), k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 →
        A' (up ⟨k, by unfold NF; omega⟩) = A (up ⟨k, by unfold NF; omega⟩) ∧ H' (up ⟨k, by unfold NF; omega⟩) = 0) ∧
      (∀ x, H' (rgP (SelBackSym.PS (pcpp := a.output r) da Pw W Ld) x) = 0) ∧
      (∀ x, A' (rgP (SelBackSym.PS (pcpp := a.output r) da Pw W Ld) x) = FactorLoop.entry (SelBackSym.PS (pcpp := a.output r) da Pw W Ld)
        (header true r.arity L target (FactorLoop.factorsAt coordinate ph ci m).length)
        (fun k => (SelBackSym.PS (pcpp := a.output r) da Pw W Ld).Desc (FactorLoop.factorsAt coordinate ph ci m)[k.val]?) Rc x) ∧
      (∀ i : Fin 3, H' (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = 0) ∧
      (∀ hm' : m < (FactorLoop.monomials coordinate ph ci).length, ∀ i : Fin 3,
        A' (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = ZeroPadding.pad Rc (RepairOrdinary.frame
          (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
            (CloseoutFinalC10SupplierCalls.coefficientEstimate ((FactorLoop.monomials coordinate ph ci)[m]).coefficient)
            0 0 ⟨i.val, by omega⟩))) := by
  -- front A, on the swapped view
  obtain ⟨Aa, sa, a129, a130, a141, a142, a185, a189, a103, a104, a200, a201, aKeep, -⟩ :=
    front_aP a r ci Rc pw (fun z => A (us z)) hc hwinA hQR hiL hiR
      (fun j => by
        have := j.isLt
        show A (up (sw ⟨j.val, _⟩)) = _
        rw [sw_ne _ (by show j.val ≠ 36; omega) (by show j.val ≠ 39; omega)]
        exact hin.cache j)
      (fun p hp => by
        show A (up (sw p)) = _
        by_cases h39 : p.val = 39
        · have e : sw p = ⟨36, by decide⟩ := Fin.ext (by show swv p.val = 36; rw [h39]; rfl)
          rw [e]; exact hin.blank 36 _ (by omega) (by omega)
        · rw [sw_ne p (by omega) h39]; exact hin.blank p.val p.isLt (by omega) h39)
  have sa' : Step (RecoveryFocus.machine (us (t := tS)) pA.2) (costA a r ci) (fun _ => 0) A (fun _ => 0)
      (install us A Aa) :=
    ((frontA_packed _ _ _ _ _ sa).dock us us_inj (fun _ => 0) A (fun _ => rfl) (fun _ => rfl)).congr
      (dockH_existing us (fun _ => 0) (fun _ => 0) (fun _ => rfl)) rfl
  have hA1 : ∀ z : Fin NF, install us A Aa (up z) = Aa (sw z) := by
    intro z; rw [up_us z]; exact install_slot us us_inj A Aa (sw z)
  have kA1 : ∀ z : Fin NF, z.val < 100 ∨ 202 ≤ z.val → install us A Aa (up z) = A (up z) := by
    intro z hz
    rw [hA1 z, aKeep (sw z) (swv_keep z.val hz)]
    show A (up (sw (sw z))) = _
    rw [sw_sw]
  have oA1 : ∀ z : Fin NF, z.val ≠ 36 → z.val ≠ 39 → install us A Aa (up z) = Aa z := by
    intro z h1 h2; rw [hA1 z, sw_ne z h1 h2]
  have rA1 : ∀ x, install us A Aa (Fin.natAdd NF x) = A (Fin.natAdd NF x) := by
    intro x
    apply install_other
    intro j e
    have hv := congrArg Fin.val e
    simp only [us, up_val, Fin.val_natAdd] at hv
    have := (sw j).isLt
    omega
  -- front B, docked by `up`
  obtain ⟨Hb, Ab, sb, b33, bcur, bcurH, bH33, bKeep⟩ :=
    front_b ph a r ci true coordinate bits hread m Rc (fun z => install us A Aa (up z)) hm hcL hcR hbig
      ((kA1 19 (by decide)).trans hin.wit) ((kA1 20 (by decide)).trans hin.cur)
      ((oA1 185 (by decide) (by decide)).trans a185) ((oA1 189 (by decide) (by decide)).trans a189)
      ((oA1 130 (by decide) (by decide)).trans a130) ((oA1 142 (by decide) (by decide)).trans a142)
      ((oA1 200 (by decide) (by decide)).trans a200) ((oA1 201 (by decide) (by decide)).trans a201)
      ((kA1 33 (by decide)).trans (hin.blank 33 _ (by omega) (by omega)))
      ((kA1 40 (by decide)).trans (hin.blank 40 _ (by omega) (by omega)))
      ((kA1 41 (by decide)).trans (hin.blank 41 _ (by omega) (by omega)))
      (fun z hz => (kA1 z (Or.inr hz)).trans (hin.blank z.val z.isLt (by omega) (by omega)))
  have sb' : Step (RecoveryFocus.machine (up (t := tS)) (pB ph).2) _ (fun _ => 0) (install us A Aa)
      (dockH up (fun _ => 0) Hb) (install up (install us A Aa) Ab) :=
    (frontB_packed ph _ _ _ _ _ sb).dock up up_inj (fun _ => 0) (install us A Aa) (fun _ => rfl) (fun _ => rfl)
  -- the bank after the front
  have hA2 : ∀ z : Fin NF, install up (install us A Aa) Ab (up z) = Ab z := fun z => install_slot up up_inj _ _ z
  have hH2 : ∀ z : Fin NF, dockH up (fun _ => 0) Hb (up (t := tS) z) = Hb z := fun z => dockH_slot up up_inj _ _ z
  have rA2 : ∀ x, install up (install us A Aa) Ab (Fin.natAdd NF x) = A (Fin.natAdd NF x) := by
    intro x
    rw [install_other up _ Ab _ (fun j e => by
      have hv := congrArg Fin.val e
      simp only [up_val, Fin.val_natAdd] at hv
      have := j.isLt
      omega)]
    exact rA1 x
  have low : ∀ z : Fin NF, z.val < 100 → z.val ≠ 33 →
      install up (install us A Aa) Ab (up z) = A (up z) := by
    intro z hz h33
    rw [hA2 z, (bKeep z (Or.inl (by omega)) (fun e => h33 (by rw [e]; rfl))).1]
    exact kA1 z (Or.inl hz)
  have mid : ∀ z : Fin NF, z.val < 300 → z.val ≠ 33 → z.val ≠ 36 → z.val ≠ 39 →
      install up (install us A Aa) Ab (up z) = Aa z := by
    intro z hz h33 h36 h39
    rw [hA2 z, (bKeep z (Or.inl hz) (fun e => h33 (by rw [e]; rfl))).1]
    exact oA1 z h36 h39
  have high : ∀ z : Fin NF, 1400 ≤ z.val → install up (install us A Aa) Ab (up z) = A (up z) := by
    intro z hz
    rw [hA2 z, (bKeep z (Or.inr hz) (fun e => by rw [e] at hz; revert hz; decide)).1]
    exact kA1 z (Or.inr (by omega))
  have headsF : ∀ z : Fin NF, ¬ (300 ≤ z.val ∧ z.val < 1400) → dockH up (fun _ => 0) Hb (up (t := tS) z) = 0 := by
    intro z hz
    rw [hH2 z]
    by_cases h33 : z = 33
    · rw [h33]; exact bH33
    · exact (bKeep z (by omega) h33).2
  -- the back's entry
  have hback : BackInK (SelBackSym.PS (pcpp := a.output r) da Pw W Ld).t true (install up (install us A Aa) Ab)
      (dockH up (fun _ => 0) Hb) (sigmaOf a r ci coordinate ph m) ph bits r.arity Pw W Ld L target cwid cw D
      (2 ^ (a.output r).clauseBits) b (literalIndex ((a.output r).clauses ci).left).val
      (literalIndex ((a.output r).clauses ci).right).val Rc
      (value a r (literalIndex ((a.output r).clauses ci).left).val)
      (value a r (literalIndex ((a.output r).clauses ci).right).val) QK := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact cursorOut_of_eq (fun j => hA2 _) bcur
    · exact (low 19 (by decide) (by decide)).trans hin.wit
    · exact (low 21 (by decide) (by decide)).trans hin.tpl
    · exact (low 22 (by decide) (by decide)).trans hin.uP
    · exact (low 23 (by decide) (by decide)).trans hin.uW
    · exact (low 24 (by decide) (by decide)).trans hin.uL
    · intro i
      have := i.isLt
      exact (low _ (by show 25 + i.val < 100; omega) (by show 25 + i.val ≠ 33; omega)).trans (hin.hdr i)
    · exact (low 29 (by decide) (by decide)).trans hin.ucwid
    · exact (low 30 (by decide) (by decide)).trans hin.ucw
    · exact (low 31 (by decide) (by decide)).trans hin.uD
    · exact (low 32 (by decide) (by decide)).trans hin.uK
    · exact (low 39 (by decide) (by decide)).trans hin.ub
    · exact (mid 129 (by decide) (by decide) (by decide) (by decide)).trans a129
    · exact (mid 141 (by decide) (by decide) (by decide) (by decide)).trans a141
    · exact (mid 103 (by decide) (by decide) (by decide) (by decide)).trans a103
    · exact (mid 104 (by decide) (by decide) (by decide) (by decide)).trans a104
    · intro i
      have := i.isLt
      exact (low _ (by show 34 + i.val < 100; omega) (by show 34 + i.val ≠ 33; omega)).trans
        (hin.blank _ _ (by omega) (by omega))
    · exact ⟨(low 42 (by decide) (by decide)).trans (hin.blank 42 _ (by omega) (by omega)),
        (low 43 (by decide) (by decide)).trans (hin.blank 43 _ (by omega) (by omega)),
        (low 44 (by decide) (by decide)).trans (hin.blank 44 _ (by omega) (by omega))⟩
    · intro k hk h1400
      exact (high ⟨k, hk⟩ h1400).trans (hin.blank k hk (by omega) (by omega))
    · intro x
      exact (rA2 x).trans (hin.region x)
    · intro z hz
      by_cases hzl : z.val < NF
      · have e : z = up ⟨z.val, hzl⟩ := Fin.ext rfl
        rw [e]
        exact headsF _ hz
      · exact dockH_other up _ Hb z (fun j e => by
          have hv := congrArg Fin.val e
          rw [up_val] at hv
          have := j.isLt
          omega)
    · intro j
      exact (hH2 _).trans (bcurH j)
  -- the back
  obtain ⟨H3, A3, s3, rH, rA, cH, cA, keep3⟩ := back_symK (pcpp := a.output r) da Pw W Ld coordinate bits hread ph ci
    (Tof coordinate ci) (eOf (a.output r) ci) rfl rfl
    (fun h => atomAt_sys (a.output r) _ h) (fun h => atomAt_sys (a.output r) _ h) m hm L target cwid cw D b Rc c QK
    (value a r (literalIndex ((a.output r).clauses ci).left).val)
    (value a r (literalIndex ((a.output r).clauses ci).right).val) hcwid h2cw
    (fun h => SourceFactorSel.SlotRead.value_eq_bitmap a r _ h)
    (fun h => SourceFactorSel.SlotRead.value_eq_bitmap a r _ h)
    ⟨(value_len a r _).trans (by omega), (value_len a r _).trans (by omega)⟩
    hwinR hqD hPD hWD hLD hDR hDC hHfit hcw1 hcoef V hV4 hcoefV hbigR (sigmaOf a r ci coordinate ph m) rfl _ _ hback
  have st := sa'.seq (sb'.seq s3)
  refine ⟨H3, A3, st, ?_, ?_, ?_, rH, rA, cH, cA⟩
  · exact (keep3 33 (by decide) (by decide) (by decide) (by decide)).2.trans (headsF 33 (by decide))
  · exact (keep3 33 (by decide) (by decide) (by decide) (by decide)).1.trans ((hA2 33).trans b33)
  · intro k hk h33 h34 h35 h36
    obtain ⟨k1, k2⟩ := keep3 k (by omega) h34 h35 h36
    refine ⟨k1.trans (low ⟨k, by unfold NF; omega⟩ hk h33), k2.trans (headsF _ (by show ¬ (300 ≤ k ∧ k < 1400); omega))⟩

/-- **`Item4.SelRun` for SYM FactorSelection, docked by `g`.** -/
theorem selRun_symP {V : Nat} (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (hread : CoordReads true coordinate bits) (ph : Phase)
    (L target cwid cw D b Rc c qCap QK : Nat) (pw : List Bool)
    (g : Fin (NF + (19 + 4 * tS)) → Fin V) (hg : Function.Injective g)
    (qTape nT : Fin V) (coefT : Fin 3 → Fin V) (hnT : g (up 33) = nT)
    (hcT : ∀ i : Fin 3, g (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = coefT i)
    (In : Nat → (Fin V → Nat) → (Fin V → List Bool) → Prop)
    (hIn : ∀ m H A, In m H A → (∀ z, H (g z) = 0) ∧
      LocalInK tS true (fun z => A (g z))
        (fun j => PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
          (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j)
        bits m r.arity Pw W Ld L target cwid cw D (2 ^ (a.output r).clauseBits) b Rc QK)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
    (hwinA : litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 1 ≤ Rc)
    (hiL : index ((a.output r).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output r).clauses ci).right + 3 ≤ Rc)
    (hcL : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).left).val + 1 ≤ Rc)
    (hcR : SourceFactorSel.CountRead.countCost bits (literalIndex ((a.output r).clauses ci).right).val + 1 ≤ Rc)
    (hbig : curBig (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length ≤ Rc)
    (hcwid : cwid = SymOriginal.symCodeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex ((a.output r).clauses ci).left).val ∨
      jj = (literalIndex ((a.output r).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : r.arity + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : ∀ m, m ≤ (FactorLoop.monomials coordinate ph ci).length →
      SourceFactorSel.HdrBlock.Fits true r.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (Vb : Nat) (hV4 : 4 ≤ Vb)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb)
    (hbigR : SourceFactorSel.CoefR.coefBigR Vb (2 ^ (a.output r).clauseBits) b (cw + rhoW) ≤ Rc) :
    SourceFactorSel.Item4.SelRun (RecoveryFocus.machine g (selSymM ph))
      (fun m => selSymCost a r ci coordinate bits ph L target cwid cw D b m)
      (SelBackSym.PS (pcpp := a.output r) da Pw W Ld) coordinate ph ci L target Rc b qCap
      (fun x => g (rgP (SelBackSym.PS (pcpp := a.output r) da Pw W Ld) x)) qTape nT coefT
      (fun x => ∃ z : Fin NF, 100 ≤ z.val ∧ g (up z) = x) In := by
  intro m hm H A hin _ _
  obtain ⟨hH0, hL⟩ := hIn m H A hin
  obtain ⟨H', A', st, h33, a33, keep, rH, rA, cH, cA⟩ := sel_sym_localP da Pw W Ld a r ci coordinate bits hread ph m hm
    L target cwid cw D b Rc c QK pw hc hwinA hQR hiL hiR hcL hcR hbig hcwid h2cw hwinR hqD hPD hWD hLD hDR hDC (hHfit m hm)
    hcw1 hcoef Vb hV4 hcoefV hbigR (fun z => A (g z)) hL
  have st' := st.dock g hg H A (fun z => hH0 z) (fun z => rfl)
  refine ⟨dockH g H H', install g A A', st', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hnT, dockH_slot g hg]; exact h33
  · rw [← hnT, install_slot g hg]; exact a33
  · intro x hreg hn hc' hscr
    by_cases hx : ∃ z, g z = x
    · obtain ⟨z, rfl⟩ := hx
      rw [install_slot g hg, dockH_slot g hg]
      by_cases hz : z.val < NF
      · have ez : z = up ⟨z.val, hz⟩ := Fin.ext rfl
        have hk100 : z.val < 100 := by
          by_contra h
          exact hscr ⟨⟨z.val, hz⟩, Nat.le_of_not_lt h, by rw [← ez]⟩
        have hk33 : z.val ≠ 33 := by
          intro e
          apply hn
          rw [← hnT]
          exact congrArg g (Fin.ext (by rw [up_val]; exact e))
        have hk3 : ∀ i : Fin 3, z.val ≠ 34 + i.val := by
          intro i e
          apply hc' i
          rw [← hcT i]
          exact congrArg g (Fin.ext (by rw [up_val]; exact e.symm))
        have h34 := hk3 0
        have h35 := hk3 1
        have h36 := hk3 2
        obtain ⟨a1, h1⟩ := keep z.val hk100 hk33 h34 h35 h36
        rw [ez]
        exact ⟨a1, h1.trans (hH0 _).symm⟩
      · exfalso
        have hPt : (SelBackSym.PS (pcpp := a.output r) da Pw W Ld).t = tS := rfl
        apply hreg ⟨z.val - NF, by have := z.isLt; rw [hPt]; unfold NF at *; omega⟩
        exact congrArg g (Fin.ext (show NF + (z.val - NF) = z.val by omega))
    · exact ⟨install_other g A A' x (fun z e => hx ⟨z, e⟩), dockH_other g H H' x (fun z e => hx ⟨z, e⟩)⟩
  · intro i; exact (dockH_slot g hg _ _ _).trans (rH i)
  · intro i; exact (install_slot g hg _ _ _).trans (rA i)
  · intro i; rw [← hcT i, dockH_slot g hg]; exact cH i
  · intro hm' i; rw [← hcT i, install_slot g hg]; exact cA hm' i

end
end NearCubicWires.SourceRequest.SelLocal

