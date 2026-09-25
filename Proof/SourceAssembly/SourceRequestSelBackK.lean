import Proof.SourceAssembly.SourceRequestSelSymRun

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack NearCubicWires.SourceRequest.SelBackSym
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

section
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- **The back's entry facts, the clause-count port at ANY padding `QK`** (S keeps `Selected.terminal = 1^(2^clauseBits)` EXACT, R-SA16:
`QK = 0`); otherwise `SelBack.BackIn` (the bank after the front; every port `pad Rc`; heads 0 outside the front's scratch `300..1399`
and on the cursor's ports). -/
structure BackInK (t : Nat) (mode : Bool) (A : Fin (NF + (19 + 4 * t)) → List Bool) (H : Fin (NF + (19 + 4 * t)) → Nat)
    (σ : Option Sel) (ph : Phase) (bits : List Bool) (q Pw W Ld L target cwid cw D K b iL iR Rc : Nat)
    (bmL bmR : List Bool) (QK : Nat) : Prop where
  cur : CursorOut σ Rc (fun j => A (up (SelFront.curSl ph j)))
  wit : A (up 19) = RepairOrdinary.frame bits
  tpl : A (up 21) = ZeroPadding.pad Rc (UnaryTemplate.tape q)
  uP : A (up 22) = ZeroPadding.pad Rc (List.replicate Pw true)
  uW : A (up 23) = ZeroPadding.pad Rc (List.replicate W true)
  uL : A (up 24) = ZeroPadding.pad Rc (List.replicate Ld true)
  hdr : ∀ i : Fin 4, A (up ⟨25 + i.val, by have := i.isLt; unfold NF; omega⟩) =
    ZeroPadding.pad Rc (RepairOrdinary.frame (SourceFactorSel.Header.fields mode q L target 0 ⟨i.val, by omega⟩))
  ucwid : A (up 29) = ZeroPadding.pad Rc (List.replicate cwid true)
  ucw : A (up 30) = ZeroPadding.pad Rc (List.replicate cw true)
  uD : A (up 31) = ZeroPadding.pad Rc (List.replicate D true)
  uK : A (up 32) = ZeroPadding.pad QK (List.replicate K true)
  ub : A (up 39) = ZeroPadding.pad Rc (List.replicate b true)
  uiL : A (up 129) = ZeroPadding.pad Rc (List.replicate iL true)
  uiR : A (up 141) = ZeroPadding.pad Rc (List.replicate iR true)
  ubL : A (up 103) = ZeroPadding.pad Rc bmL
  ubR : A (up 104) = ZeroPadding.pad Rc bmR
  coefT : ∀ i : Fin 3, A (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = List.replicate Rc false
  logs : A (up 42) = List.replicate Rc false ∧ A (up 43) = List.replicate Rc false ∧ A (up 44) = List.replicate Rc false
  hi : ∀ k (h : k < NF), 1400 ≤ k → A (up ⟨k, h⟩) = List.replicate Rc false
  region : ∀ x, A (Fin.natAdd NF x) = List.replicate Rc false
  heads : ∀ z : Fin (NF + (19 + 4 * t)), ¬ (300 ≤ z.val ∧ z.val < 1400) → H z = 0
  curH : ∀ j : Fin 128, H (up (SelFront.curSl ph j)) = 0

theorem four_thrK (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hread : CoordReads false coordinate bits) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (e : Bool → RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length)
    (L target cwid cw D K b Rc QK : Nat) (bmL bmR : List Bool)
    (hcwid : cwid = ThrSwitch.codeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hbmL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      bmL = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      bmR = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmD : bmL.length ≤ D ∧ bmR.length ≤ D)
    (hwin : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex (pcpp.clauses ci).left).val ∨
      jj = (literalIndex (pcpp.clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : n0 + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (σ : Option Sel)
    (hσ : σ = selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m)
    (A : Fin (NF + (19 + 4 * (PT (pcpp := pcpp) da Pw W Ld).t)) → List Bool)
    (H : Fin (NF + (19 + 4 * (PT (pcpp := pcpp) da Pw W Ld).t)) → Nat)
    (hin : BackInK (PT (pcpp := pcpp) da Pw W Ld).t false A H σ ph bits n0 Pw W Ld L target cwid cw D K b
      (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val Rc bmL bmR QK) :
    ∃ (H1 : Fin (NF + (19 + 4 * (PT (pcpp := pcpp) da Pw W Ld).t)) → Nat)
      (A1 : Fin (NF + (19 + 4 * (PT (pcpp := pcpp) da Pw W Ld).t)) → List Bool),
      Step (SourceFactorSel.Slots4.fourM (slB (PT (pcpp := pcpp) da Pw W Ld) rfl))
        (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 0) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ 0)) cwid cw D + 1 +
          (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 1) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ 1)) cwid cw D + 1 +
          (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 2) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ 2)) cwid cw D + 1 +
          SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 3) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ 3)) cwid cw D))) H A H1 A1 ∧
      (∀ (i : Fin 4) (n : Fin 16),
        A1 (rgP _ (FactorLoop.cslot (PT (pcpp := pcpp) da Pw W Ld) i ((PT (pcpp := pcpp) da Pw W Ld).descSlots n))) =
          ZeroPadding.pad Rc ((PT (pcpp := pcpp) da Pw W Ld).Desc ((FactorLoop.factorsAt coordinate ph ci m)[i.val]?) n) ∧
        H1 (rgP _ (FactorLoop.cslot (PT (pcpp := pcpp) da Pw W Ld) i ((PT (pcpp := pcpp) da Pw W Ld).descSlots n))) = 0) ∧
      (∀ i : Fin 4, fTerm (facAt σ i.val) = true →
        A1 (up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩) = ZeroPadding.pad Rc
          (RepairOrdinary.CloseoutRowsEstimatorCoefficients.Product.record cw
            (SourceFactorSel.CoefBridge.tco T (facAt σ i.val)))) ∧
      (∀ i : Fin 4, H1 (up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩) = 0) ∧
      (∀ x, SourceFactorSel.Slots4.Kept (slB (PT (pcpp := pcpp) da Pw W Ld) rfl) x → A1 x = A x ∧ H1 x = H x) := by
  have hyp := fun i : Fin 4 => slot_hyps_thr coordinate bits hread ph ci T e hTL hTR heL heR m hm Ld cwid cw D Rc hcwid
    h2cw bmL bmR hbmL hbmR hbmD hwin i σ hσ
  have hRc1 : 1 ≤ Rc := by omega
  obtain ⟨cs, ct, cr, ci', ck, crho⟩ := hin.cur
  obtain ⟨H1, A1, st, hdesc, hrec, hrecH, hkept⟩ := SourceFactorSel.Slots4.thr_four (slB (PT (pcpp := pcpp) da Pw W Ld) rfl) (slB_inj (PT (pcpp := pcpp) da Pw W Ld) rfl)
    (slB_disj (PT (pcpp := pcpp) da Pw W Ld) rfl) Pw W Ld (fun i => (FactorLoop.factorsAt coordinate ph ci m)[i.val]?) bmL bmR bits
    (fun i => fSys (facAt σ i.val)) (fun i => fTerm (facAt σ i.val)) (fun i => fSide (facAt σ i.val))
    (fun i => fIdx (facAt σ i.val)) (literalIndex (pcpp.clauses ci).left).val
    (literalIndex (pcpp.clauses ci).right).val cwid cw D Rc Rc Rc Rc Rc Rc Rc Rc 0 Rc Rc H A
    (by
      intro i j
      have := i.isLt; have := j.isLt
      by_cases hj4 : j.val < 4
      · rw [slB_curv da Pw W Ld ph i j hj4 ⟨6 + 4 * i.val + j.val, by omega⟩ rfl]
        exact hin.curH _
      apply hin.heads
      by_cases hj : 17 ≤ j.val ∧ j.val < 33
      · rw [slB_rg (PT (pcpp := pcpp) da Pw W Ld) rfl i j hj.1 hj.2, rg_val]; unfold NF; omega
      · rw [slB_lo (PT (pcpp := pcpp) da Pw W Ld) rfl i j hj]
        rcases loVal_cases i.val j.val i.isLt hj with ⟨h1, e1, -⟩ | ⟨-, e1⟩ | ⟨-, e1⟩ <;> rw [e1]
        · have := inPort_heads i.val i.isLt j.val h1 (by omega); omega
        · omega
        · omega)
    (fun i => (congrArg A (slB_curv da Pw W Ld ph i 0 (by decide) (sysT i) (by simp [sysT]))).trans (cs i))
    (fun i => (congrArg A (slB_curv da Pw W Ld ph i 1 (by decide) (termT i) (by simp [termT]; omega))).trans (ct i))
    (fun i => (congrArg A (slB_curv da Pw W Ld ph i 2 (by decide) (rightT i) (by simp [rightT]; omega))).trans (cr i))
    hRc1
    (by
      intro i
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (congrArg A (slB_curv da Pw W Ld ph i 3 (by decide) (idxT i) (by simp [idxT]; omega))).trans (ci' i)
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨4, by decide⟩) = _; rw [slB_in da Pw W Ld i 4 (by decide) (by decide)]; exact hin.uiL
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨5, by decide⟩) = _; rw [slB_in da Pw W Ld i 5 (by decide) (by decide)]; exact hin.uiR
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨6, by decide⟩) = _; rw [slB_in da Pw W Ld i 6 (by decide) (by decide)]; exact hin.ubL
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨7, by decide⟩) = _; rw [slB_in da Pw W Ld i 7 (by decide) (by decide)]; exact hin.ubR
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨8, by decide⟩) = _; rw [slB_in da Pw W Ld i 8 (by decide) (by decide), ZeroPadding.pad_zero]
        exact hin.wit
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨9, by decide⟩) = _; rw [slB_in da Pw W Ld i 9 (by decide) (by decide)]; exact hin.ucwid
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨10, by decide⟩) = _; rw [slB_in da Pw W Ld i 10 (by decide) (by decide)]; exact hin.ucw
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨11, by decide⟩) = _; rw [slB_in da Pw W Ld i 11 (by decide) (by decide)]; exact hin.tpl
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨12, by decide⟩) = _; rw [slB_in da Pw W Ld i 12 (by decide) (by decide)]; exact hin.uP
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨13, by decide⟩) = _; rw [slB_in da Pw W Ld i 13 (by decide) (by decide)]; exact hin.uW
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨14, by decide⟩) = _; rw [slB_in da Pw W Ld i 14 (by decide) (by decide)]; exact hin.uL
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨15, by decide⟩) = _; rw [slB_in da Pw W Ld i 15 (by decide) (by decide)]; exact hin.uD
      · show A (slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨16, by decide⟩) = _; rw [slB_in da Pw W Ld i 16 (by decide) (by decide)]; exact hin.logs.1
      · intro j hj
        have := i.isLt; have := j.isLt
        by_cases hj' : j.val < 33
        · rw [slB_rg (PT (pcpp := pcpp) da Pw W Ld) rfl i j hj hj']; exact hin.region _
        · have e : slB (PT (pcpp := pcpp) da Pw W Ld) rfl i j = up ⟨loVal i.val j.val, by
              rcases loVal_cases i.val j.val i.isLt (by omega) with ⟨h1, e1, -⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1] <;>
                unfold NF <;> omega⟩ := Fin.ext (by rw [slB_lo (PT (pcpp := pcpp) da Pw W Ld) rfl i j (by omega)]; rfl)
          rw [e]
          apply hin.hi
          rcases loVal_cases i.val j.val i.isLt (by omega) with ⟨h1, e1, -⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1] <;> omega)
    hqD hPD hWD hLD hDR hDC (fun i => (hyp i).1) (fun i => (hyp i).2.1) (fun i => (hyp i).2.2.1)
    (fun i => (hyp i).2.2.2.1)
  refine ⟨H1, A1, st, ?_, ?_, ?_, hkept⟩
  · intro i n
    have e : slB (PT (pcpp := pcpp) da Pw W Ld) rfl i (SourceFactorSel.Slot.outP n) =
        rgP (PT (pcpp := pcpp) da Pw W Ld) (FactorLoop.cslot (PT (pcpp := pcpp) da Pw W Ld) i ((PT (pcpp := pcpp) da Pw W Ld).descSlots n)) := by
      rw [slB_rg (PT (pcpp := pcpp) da Pw W Ld) rfl i _ (by simp [SourceFactorSel.Slot.outP]) (by simp [SourceFactorSel.Slot.outP]; omega)]
      congr 3
      apply Fin.ext; simp [SourceFactorSel.Slot.outP]
    rw [← e]; exact hdesc i n
  · intro i ht
    obtain ⟨ts, hi, hraw, -⟩ := (hyp i).2.2.2.1 ht
    have e33 : slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨33, by decide⟩ = up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩ :=
      Fin.ext (by rw [slB_lo (PT (pcpp := pcpp) da Pw W Ld) rfl i _ (by simp), up_val]; simp [loVal])
    rw [← e33, (hyp i).2.2.2.2 ht ts hraw hi]
    exact hrec i ht ts hraw hi
  · intro i
    have e33 : slB (PT (pcpp := pcpp) da Pw W Ld) rfl i ⟨33, by decide⟩ = up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩ :=
      Fin.ext (by rw [slB_lo (PT (pcpp := pcpp) da Pw W Ld) rfl i _ (by simp), up_val]; simp [loVal])
    rw [← e33]; exact hrecH i

/-- **The header stage on the local universe** (after the slots): writes `frame (header mode q L target k)` on region
port `0`; keeps every fixed port outside `6008..6034` and every other region port. -/
theorem hdr_stageK {mode : Bool} {da : RepairRepresentation.DecompositionAlgorithm}
    (P : FactorLoop.FactorProducer mode da pcpp) (Pw W Ld : Nat) (σ : Option Sel) (ph : Phase)
    (bits : List Bool) (q L target cwid cw D K b iL iR Rc c QK : Nat) (bmL bmR : List Bool)
    (A A1 : Fin (NF + (19 + 4 * P.t)) → List Bool)
    (H H1 : Fin (NF + (19 + 4 * P.t)) → Nat)
    (hin : BackInK P.t mode A H σ ph bits q Pw W Ld L target cwid cw D K b iL iR Rc bmL bmR QK)
    (kv : ∀ x : Fin (NF + (19 + 4 * P.t)),
      x.val < 1400 ∨ (6000 ≤ x.val ∧ x.val < NF) → A1 x = A x ∧ H1 x = H x)
    (r0 : A1 (rgP _ ⟨0, by omega⟩) = List.replicate Rc false ∧ H1 (rgP _ ⟨0, by omega⟩) = 0)
    (k : Nat) (hk : k = kOf σ) (hfit : SourceFactorSel.HdrBlock.Fits mode q L target k c D Rc Rc Rc Rc) :
    ∃ A2 : Fin (NF + (19 + 4 * P.t)) → List Bool,
      Step (RecoveryFocus.machine (hdSl P) SourceFactorSel.HdrBlock.hdrM)
        (SourceFactorSel.HdrBlock.hdrCost mode q L target k D) H1 A1 H1 A2 ∧
      A2 (rgP _ ⟨0, by omega⟩) = ZeroPadding.pad Rc (RepairOrdinary.frame (header mode q L target k)) ∧
      (∀ x : Fin (NF + (19 + 4 * P.t)), x.val < NF →
        (x.val < 6008 ∨ 6035 ≤ x.val) → A2 x = A1 x) ∧
      (∀ x : Fin (19 + 4 * P.t), x.val ≠ 0 → A2 (rgP _ x) = A1 (rgP _ x)) := by
  have hd7 : hdSl P 7 = rgP _ ⟨0, by omega⟩ := Fin.ext (by rw [hdSl_val, rg_val]; rfl)
  obtain ⟨cs, ct, cr, ci', ck, crho⟩ := hin.cur
  have hd0 : hdSl P 0 = up (SelFront.curSl ph kT) :=
    Fin.ext (by rw [hdSl_val, up_val, SelFront.curSl_val]; rfl)
  have hH1 : ∀ j, H1 (hdSl P j) = 0 := by
    intro j
    by_cases h7 : j.val = 7
    · have e7 : j = 7 := Fin.ext h7
      rw [e7, hd7]; exact r0.2
    · have hv := hdSl_val P j
      have := j.isLt
      have hlo : (hdSl P j).val < 1400 ∨
          (6000 ≤ (hdSl P j).val ∧ (hdSl P j).val < NF) := by
        rw [hv]; split_ifs <;> (try unfold NF) <;> omega
      rw [(kv _ hlo).2]
      by_cases hj0 : j.val = 0
      · have e0 : j = 0 := Fin.ext hj0
        rw [e0, hd0]; exact hin.curH kT
      · exact hin.heads _ (by rw [hv]; split_ifs <;> (try unfold NF) <;> omega)
  have h0 : A1 (hdSl P 0) = ZeroPadding.pad Rc (List.replicate k true) := by
    rw [(kv _ (Or.inl (by rw [hdSl_val]; decide))).1, hd0, hk]; exact ck
  have hf : ∀ i : Fin 4, A1 (hdSl P ⟨i.val + 1, by omega⟩) =
      ZeroPadding.pad Rc (RepairOrdinary.frame (SourceFactorSel.Header.fields mode q L target k ⟨i.val, by omega⟩)) := by
    intro i
    have := i.isLt
    have hv : (hdSl P ⟨i.val + 1, by omega⟩).val = 25 + i.val := by
      rw [hdSl_val]; split_ifs <;> simp at * <;> omega
    rw [(kv _ (Or.inl (by rw [hv]; omega))).1]
    have ei : hdSl P ⟨i.val + 1, by omega⟩ =
        up ⟨25 + i.val, by unfold NF; omega⟩ := Fin.ext (by rw [hv, up_val])
    rw [ei, hin.hdr i]
    fin_cases i <;> rfl
  have h5 : A1 (hdSl P 5) = ZeroPadding.pad Rc (List.replicate D true) := by
    rw [(kv _ (Or.inl (by rw [hdSl_val]; decide))).1]
    have e5 : hdSl P 5 = up 31 := Fin.ext (by rw [hdSl_val, up_val]; rfl)
    rw [e5]; exact hin.uD
  have h6 : A1 (hdSl P 6) = List.replicate Rc false := by
    rw [(kv _ (Or.inl (by rw [hdSl_val]; decide))).1]
    have e6 : hdSl P 6 = up 43 := Fin.ext (by rw [hdSl_val, up_val]; rfl)
    rw [e6]; exact hin.logs.2.1
  have h7 : A1 (hdSl P 7) = List.replicate Rc false := by
    rw [hd7]; exact r0.1
  have hscr : ∀ j : Fin 35, 8 ≤ j.val → A1 (hdSl P j) = List.replicate Rc false := by
    intro j hj
    have := j.isLt
    have hv : (hdSl P j).val = 6000 + j.val := by
      rw [hdSl_val]; split_ifs <;> omega
    rw [(kv _ (Or.inr (by rw [hv]; unfold NF; omega))).1,
      up_of (hdSl P j) (by rw [hv]; unfold NF; omega)]
    exact hin.hi _ _ (by rw [hv]; omega)
  obtain ⟨A2, s2, o2, kp2⟩ := SourceFactorSel.HdrBlock.hdr_step (hdSl P)
    (hdSl_inj P) mode q L target k c D
    Rc Rc Rc Rc Rc Rc H1 A1 hH1 h0 hf h5 h6 h7 hscr hfit
  refine ⟨A2, s2, by rw [← hd7]; exact o2, ?_, ?_⟩
  · intro x h1 h2
    apply kp2
    intro j ej
    have hv := congrArg Fin.val ej
    rw [hdSl_val] at hv
    have := j.isLt
    by_contra hj
    split_ifs at hv <;> (try unfold NF at *) <;> omega
  · intro x hx
    apply kp2
    intro j ej
    have hv := congrArg Fin.val ej
    rw [hdSl_val, rg_val] at hv
    have := j.isLt
    by_contra hj
    split_ifs at hv <;> (try unfold NF at *) <;> omega

/-- **The coefficient stage on the local universe, sized by a value bound `V`** (any producer, any mode): as
`SelBack.coef_stage`, with the window `coefBigR V K b (cw + rhoW) ≤ Rc` in place of `coefBigR (2^cw + 4) …`. -/
theorem coef_stageK {mode : Bool} {da : RepairRepresentation.DecompositionAlgorithm}
    (P : FactorLoop.FactorProducer mode da pcpp) (Pw W Ld : Nat) (σ : Option Sel) (ph : Phase)
    (bits : List Bool) (q L target cwid cw D K b iL iR Rc QK : Nat) (bmL bmR : List Bool)
    (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (A A1 A2 : Fin (NF + (19 + 4 * P.t)) → List Bool)
    (H H1 : Fin (NF + (19 + 4 * P.t)) → Nat)
    (hin : BackInK P.t mode A H σ ph bits q Pw W Ld L target cwid cw D K b iL iR Rc bmL bmR QK)
    (kv : ∀ x : Fin (NF + (19 + 4 * P.t)),
      x.val < 1400 ∨ (6000 ≤ x.val ∧ x.val < NF) → A1 x = A x ∧ H1 x = H x)
    (hrec : ∀ i : Fin 4, fTerm (facAt σ i.val) = true →
      A1 (up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩) = ZeroPadding.pad Rc
        (CloseoutRowsEstimatorCoefficients.Product.record cw (SourceFactorSel.CoefBridge.tco T (facAt σ i.val))))
    (hrecH : ∀ i : Fin 4, H1 (up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩) = 0)
    (kp2 : ∀ x : Fin (NF + (19 + 4 * P.t)), x.val < NF →
      (x.val < 6008 ∨ 6035 ≤ x.val) → A2 x = A1 x)
    (hcw1 : 1 ≤ cw) (hT : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (V : Nat) (hV4 : 4 ≤ V) (hTV : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < V ∧ mo.coefficient.den < V)
    (hrb : (rhoOf σ).num.natAbs < 2 ^ rhoW ∧ (rhoOf σ).den < 2 ^ rhoW) (hK0 : 0 < K)
    (hbigR : SourceFactorSel.CoefR.coefBigR V K b (cw + rhoW) ≤ Rc) :
    ∃ A3 : Fin (NF + (19 + 4 * P.t)) → List Bool,
      Step (RecoveryFocus.machine (cfSl P) SourceFactorSel.CoefR.coefRM)
        (SourceFactorSel.CoefR.coefRCost cw rhoW K b (rhoOf σ) (fun i => fTerm (facAt σ i.val))
          (fun i => SourceFactorSel.CoefBridge.tco T (facAt σ i.val))) H1 A2 H1 A3 ∧
      (∀ i : Fin 3, A3 (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) =
        SourceFactorSel.Coef.coefWord b Rc (SourceFactorSel.CoefR.coefOfR K (rhoOf σ)
          (fun i => fTerm (facAt σ i.val)) (fun i => SourceFactorSel.CoefBridge.tco T (facAt σ i.val))) i) ∧
      (∀ x : Fin (NF + (19 + 4 * P.t)),
        (x.val < 34 ∨ (37 ≤ x.val ∧ x.val < 6115) ∨ NF ≤ x.val) → A3 x = A2 x) := by
  obtain ⟨cs, ct, cr, ci', ck, crho⟩ := hin.cur
  have hbits : ∀ i : Fin 4, fTerm (facAt σ i.val) = true →
      (SourceFactorSel.CoefBridge.tco T (facAt σ i.val)).num.natAbs < 2 ^ cw ∧
        (SourceFactorSel.CoefBridge.tco T (facAt σ i.val)).den < 2 ^ cw :=
    fun i _ => tco_bits T cw hcw1 hT (facAt σ i.val)
  have h4 : 2 ^ rhoW = 4 := rfl
  have hfit := SourceFactorSel.CoefR.coefFitsR_of_big cw rhoW K b V (rhoOf σ)
    (fun i => fTerm (facAt σ i.val)) (fun i => SourceFactorSel.CoefBridge.tco T (facAt σ i.val)) Rc Rc (by omega)
    (fun i _ => tco_V T V (by omega) hTV (facAt σ i.val))
    ⟨by have := hrb.1; omega, by have := hrb.2; omega⟩ hbits hbigR hbigR
  have hH2 : ∀ j, H1 (cfSl P j) = 0 := by
    intro j
    have hv := cfSl_cfv P j
    have := j.isLt
    by_cases hj4 : j.val < 4
    · have ej : cfSl P j = up ⟨1400 + (⟨j.val, hj4⟩ : Fin 4).val, by unfold NF; omega⟩ :=
        Fin.ext (by rw [hv, up_val]; simp only [cfv, if_pos hj4])
      rw [ej]; exact hrecH ⟨j.val, hj4⟩
    · have hlo : (cfSl P j).val < 1400 ∨ (6000 ≤ (cfSl P j).val ∧ (cfSl P j).val < NF) := by
        rw [hv]; exact cfv_lo j.val j.isLt (by omega)
      rw [(kv _ hlo).2]
      by_cases hj8 : j.val < 8
      · have ej : cfSl P j = up (SelFront.curSl ph (termT ⟨j.val - 4, by omega⟩)) :=
          Fin.ext (by
            rw [hv, up_val, curSl_hi ph _ (by show 6 ≤ 7 + 4 * (j.val - 4); omega),
              cfv_mid j.val j.isLt (by omega) hj8]
            rfl)
        rw [ej]; exact hin.curH _
      by_cases hj9 : j.val = 8
      · have e8 : j = 8 := Fin.ext hj9
        have ej : cfSl P 8 = up (SelFront.curSl ph rhoT) :=
          Fin.ext (by rw [cfSl_val, up_val, SelFront.curSl_val]; rfl)
        rw [e8, ej]; exact hin.curH _
      exact hin.heads _ (by rw [hv]; exact cfv_heads j.val j.isLt (by omega))
  have cv : ∀ j : Fin 245, 4 ≤ j.val → A2 (cfSl P j) = A (cfSl P j) := by
    intro j hj
    have hv := cfSl_cfv P j
    obtain ⟨c1, c2⟩ := cfv_cv j.val j.isLt hj
    rw [kp2 _ (by rw [hv]; exact c2) (by rw [hv]; exact c1)]
    exact (kv _ (by rw [hv]; exact cfv_lo j.val j.isLt hj)).1
  have hrecQ : ∀ i : Fin 4, fTerm (facAt σ i.val) = true →
      A2 (cfSl P (SourceFactorSel.CoefR.recQ i)) =
        ZeroPadding.pad Rc (CloseoutRowsEstimatorCoefficients.Product.record cw
          (SourceFactorSel.CoefBridge.tco T (facAt σ i.val))) := by
    intro i hi
    have := i.isLt
    have hv : (cfSl P (SourceFactorSel.CoefR.recQ i)).val = 1400 + i.val := by
      rw [cfSl_val]; fin_cases i <;> rfl
    rw [kp2 _ (by rw [hv]; unfold NF; omega) (by rw [hv]; omega)]
    have ei : cfSl P (SourceFactorSel.CoefR.recQ i) =
        up ⟨1400 + i.val, by unfold NF; omega⟩ := Fin.ext (by rw [hv, up_val])
    rw [ei]; exact hrec i hi
  have hflag : ∀ i : Fin 4, A2 (cfSl P (SourceFactorSel.CoefR.flagQ i)) =
      ZeroPadding.pad Rc [fTerm (facAt σ i.val)] := by
    intro i
    have hq : 4 ≤ (SourceFactorSel.CoefR.flagQ i).val := by fin_cases i <;> decide
    rw [cv _ hq]
    have ei : cfSl P (SourceFactorSel.CoefR.flagQ i) = up (SelFront.curSl ph (termT i)) :=
      Fin.ext (by rw [cfSl_val, up_val, SelFront.curSl_val]; fin_cases i <;> rfl)
    rw [ei]; exact ct i
  have hrho : A2 (cfSl P 8) =
      ZeroPadding.pad Rc (CloseoutRowsEstimatorCoefficients.Product.record rhoW (rhoOf σ)) := by
    rw [cv _ (by decide)]
    have ei : cfSl P 8 = up (SelFront.curSl ph rhoT) :=
      Fin.ext (by rw [cfSl_val, up_val, SelFront.curSl_val]; rfl)
    rw [ei]; exact crho
  have hKp : A2 (cfSl P 9) = ZeroPadding.pad QK (List.replicate K true) := by
    rw [cv _ (by decide)]
    have ei : cfSl P 9 = up 32 := Fin.ext (by rw [cfSl_val, up_val]; rfl)
    rw [ei]; exact hin.uK
  have hbp : A2 (cfSl P 10) = ZeroPadding.pad Rc (List.replicate b true) := by
    rw [cv _ (by decide)]
    have ei : cfSl P 10 = up 39 := Fin.ext (by rw [cfSl_val, up_val]; rfl)
    rw [ei]; exact hin.ub
  have hout : ∀ i : Fin 3, A2 (cfSl P (SourceFactorSel.CoefR.outQ i)) =
      List.replicate Rc false := by
    intro i
    have := i.isLt
    have hq : 4 ≤ (SourceFactorSel.CoefR.outQ i).val := by fin_cases i <;> decide
    rw [cv _ hq]
    have ei : cfSl P (SourceFactorSel.CoefR.outQ i) =
        up ⟨34 + i.val, by unfold NF; omega⟩ := Fin.ext (by rw [cfSl_val, up_val]; fin_cases i <;> rfl)
    rw [ei]; exact hin.coefT i
  have hlog : A2 (cfSl P 14) = List.replicate Rc false := by
    rw [cv _ (by decide)]
    have ei : cfSl P 14 = up 44 := Fin.ext (by rw [cfSl_val, up_val]; rfl)
    rw [ei]; exact hin.logs.2.2
  have hscr2 : ∀ j : Fin 245, 15 ≤ j.val → A2 (cfSl P j) = List.replicate Rc false := by
    intro j hj
    have := j.isLt
    rw [cv _ (by omega)]
    have hv' : (cfSl P j).val = 6100 + j.val := by rw [cfSl_cfv]; exact cfv_hi j.val j.isLt hj
    rw [up_of (cfSl P j) (by rw [hv']; unfold NF; omega)]
    exact hin.hi _ _ (by rw [hv']; omega)
  obtain ⟨A3, s3, o3, kp3⟩ := SourceFactorSel.CoefR.coefR_step (cfSl P)
    (cfSl_inj P) cw rhoW K b Rc Rc Rc QK Rc Rc Rc Rc (rhoOf σ)
    (fun i => fTerm (facAt σ i.val)) (fun i => SourceFactorSel.CoefBridge.tco T (facAt σ i.val)) H1 A2 hH2
    hrecQ hflag hrho hKp hbp hout hlog hscr2 hbits hrb hK0 hfit
  refine ⟨A3, s3, ?_, ?_⟩
  · intro i
    have ei : up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩ =
        cfSl P (SourceFactorSel.CoefR.outQ i) :=
      Fin.ext (by rw [cfSl_val, up_val]; fin_cases i <;> rfl)
    rw [ei]; exact o3 i
  · intro x hx
    apply kp3
    intro j ej
    by_contra hj
    have hv := congrArg Fin.val ej
    rw [cfSl_cfv] at hv
    rcases cfv_frame j.val j.isLt hj with h | h
    · rw [hv] at h; unfold NF at hx; omega
    · rw [hv] at h; unfold NF at hx; omega

/-- **FactorSelection's back, THR mode, value-bounded, on the packed machine `backP da`.** As `SelBack.back_thr`, with the
coefficient window at the value bound `V` (`hV4`, `hcoefV`, `hbigR`). -/
theorem back_thrK (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hread : CoordReads false coordinate bits) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (e : Bool → RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length)
    (L target cwid cw D b Rc c QK : Nat) (bmL bmR : List Bool)
    (hcwid : cwid = ThrSwitch.codeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hbmL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      bmL = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      bmR = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmD : bmL.length ≤ D ∧ bmR.length ≤ D)
    (hwin : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex (pcpp.clauses ci).left).val ∨
      jj = (literalIndex (pcpp.clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : n0 + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : SourceFactorSel.HdrBlock.Fits false n0 L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc
      Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (V : Nat) (hV4 : 4 ≤ V)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < V ∧ mo.coefficient.den < V)
    (hbigR : SourceFactorSel.CoefR.coefBigR V (2 ^ pcpp.clauseBits) b (cw + rhoW) ≤ Rc)
    (σ : Option Sel)
    (hσ : σ = selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m)
    (A : Fin (NF + (19 + 4 * tT da)) → List Bool)
    (H : Fin (NF + (19 + 4 * tT da)) → Nat)
    (hin : BackInK (PT (pcpp := pcpp) da Pw W Ld).t false A H σ ph bits n0 Pw W Ld L target cwid cw D
      (2 ^ pcpp.clauseBits) b (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val Rc
      bmL bmR QK) :
    ∃ (H' : Fin (NF + (19 + 4 * tT da)) → Nat) (A' : Fin (NF + (19 + 4 * tT da)) → List Bool),
      Step (backP da)
        (backThrCost T bits (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val σ
          cwid cw D n0 L target (FactorLoop.factorsAt coordinate ph ci m).length (2 ^ pcpp.clauseBits) b) H A H' A' ∧
      (∀ x, H' (rgP (PT (pcpp := pcpp) da Pw W Ld) x) = 0) ∧
      (∀ x, A' (rgP (PT (pcpp := pcpp) da Pw W Ld) x) = FactorLoop.entry (PT (pcpp := pcpp) da Pw W Ld)
        (header false n0 L target (FactorLoop.factorsAt coordinate ph ci m).length)
        (fun k => (PT (pcpp := pcpp) da Pw W Ld).Desc (FactorLoop.factorsAt coordinate ph ci m)[k.val]?) Rc x) ∧
      (∀ i : Fin 3, H' (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = 0) ∧
      (∀ hm' : m < (FactorLoop.monomials coordinate ph ci).length, ∀ i : Fin 3,
        A' (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = ZeroPadding.pad Rc (RepairOrdinary.frame
          (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
            (CloseoutFinalC10SupplierCalls.coefficientEstimate ((FactorLoop.monomials coordinate ph ci)[m]).coefficient)
            0 0 ⟨i.val, by omega⟩))) ∧
      (∀ k (hk : k < 1400), k ≠ 34 → k ≠ 35 → k ≠ 36 →
        A' (up ⟨k, by unfold NF; omega⟩) = A (up ⟨k, by unfold NF; omega⟩) ∧
        H' (up ⟨k, by unfold NF; omega⟩) = H (up ⟨k, by unfold NF; omega⟩)) := by
  obtain ⟨H1, A1, s1, hdesc, hrec, hrecH, kept1⟩ := four_thrK da Pw W Ld coordinate bits hread ph ci T e hTL hTR heL heR
    m hm L target cwid cw D (2 ^ pcpp.clauseBits) b Rc QK bmL bmR hcwid h2cw hbmL hbmR hbmD hwin hqD hPD hWD hLD hDR hDC σ hσ
    A H hin
  have kv : ∀ x : Fin (NF + (19 + 4 * (PT (pcpp := pcpp) da Pw W Ld).t)),
      x.val < 1400 ∨ (6000 ≤ x.val ∧ x.val < NF) → A1 x = A x ∧ H1 x = H x := by
    intro x hx
    rw [up_of x (hx.elim (fun h => Nat.lt_of_lt_of_le h (by decide)) (fun h => h.2))]
    exact kept1 _ (kept_lo da Pw W Ld x.val hx)
  have rkept : ∀ x : Fin (19 + 4 * (PT (pcpp := pcpp) da Pw W Ld).t),
      (∀ i n, FactorLoop.cslot (PT (pcpp := pcpp) da Pw W Ld) i ((PT (pcpp := pcpp) da Pw W Ld).descSlots n) ≠ x) →
      A1 (rgP _ x) = List.replicate Rc false ∧ H1 (rgP _ x) = 0 := by
    intro x hx
    obtain ⟨a1, h1⟩ := kept1 _ (kept_rg da Pw W Ld x hx)
    exact ⟨a1.trans (hin.region x), h1.trans (hin.heads _ (by rw [rg_val]; unfold NF; omega))⟩
  have c0ne : ∀ i n, FactorLoop.cslot (PT (pcpp := pcpp) da Pw W Ld) i ((PT (pcpp := pcpp) da Pw W Ld).descSlots n) ≠
      ⟨0, by omega⟩ := by
    intro i n e0
    have := FactorLoop.cslot_ge (PT (pcpp := pcpp) da Pw W Ld) i ((PT (pcpp := pcpp) da Pw W Ld).descSlots n)
    rw [e0] at this; simp at this
  have hlen : (FactorLoop.factorsAt coordinate ph ci m).length = kOf σ := by
    rw [hσ]; exact SourceFactorSel.KBridge.factorsAt_len false pcpp coordinate bits hread ph ci T e hTL hTR heL heR m hm
  obtain ⟨A2, s2, o2, kp2, kp2r⟩ := hdr_stageK (PT (pcpp := pcpp) da Pw W Ld) Pw W Ld σ ph bits n0 L target cwid cw D
    (2 ^ pcpp.clauseBits) b (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val Rc c QK
    bmL bmR A A1 H H1 hin kv (rkept _ c0ne) _ hlen hHfit
  have hT : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw := by
    intro r mo hmo
    cases r with
    | false => rw [hTL] at hmo; exact hcoef _ mo hmo
    | true => rw [hTR] at hmo; exact hcoef _ mo hmo
  have hTV : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < V ∧ mo.coefficient.den < V := by
    intro r mo hmo
    cases r with
    | false => rw [hTL] at hmo; exact hcoefV _ mo hmo
    | true => rw [hTR] at hmo; exact hcoefV _ mo hmo
  have hrb : (rhoOf σ).num.natAbs < 2 ^ rhoW ∧ (rhoOf σ).den < 2 ^ rhoW := by
    rw [hσ]; exact SelRho.rho_bits _ _ _ _ _ _ _ _
  obtain ⟨A3, s3, o3, kp3⟩ := coef_stageK (PT (pcpp := pcpp) da Pw W Ld) Pw W Ld σ ph bits n0 L target cwid cw D
    (2 ^ pcpp.clauseBits) b (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val Rc QK
    bmL bmR T A A1 A2 H H1 hin kv hrec hrecH kp2 hcw1 hT V hV4 hTV hrb (Nat.two_pow_pos _) hbigR
  have st := (four_packed pcpp da Pw W Ld _ H H1 A A1 s1).seq
    ((hdr_packed pcpp da Pw W Ld _ H1 H1 A1 A2 s2).seq (coef_packed pcpp da Pw W Ld _ H1 H1 A2 A3 s3))
  refine ⟨H1, A3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold backThrCost fourCostT
    exact st
  · intro x
    by_cases hx : ∃ i n, FactorLoop.cslot (PT (pcpp := pcpp) da Pw W Ld) i ((PT (pcpp := pcpp) da Pw W Ld).descSlots n) = x
    · obtain ⟨i, n, rfl⟩ := hx
      exact (hdesc i n).2
    · exact (rkept x (fun i n e => hx ⟨i, n, e⟩)).2
  · apply SourceFactorSel.Modes.entry_of_ports (PT (pcpp := pcpp) da Pw W Ld) (rgP _)
    · rw [kp3 _ (Or.inr (Or.inr (by rw [rg_val]; omega)))]; exact o2
    · intro i n
      rw [kp3 _ (Or.inr (Or.inr (by rw [rg_val]; omega))),
        kp2r _ (by have := FactorLoop.cslot_ge (PT (pcpp := pcpp) da Pw W Ld) i ((PT (pcpp := pcpp) da Pw W Ld).descSlots n); omega)]
      exact (hdesc i n).1
    · intro x hx0 hx
      rw [kp3 _ (Or.inr (Or.inr (by rw [rg_val]; omega))), kp2r _ hx0]
      exact (rkept x hx).1
  · intro i
    have := i.isLt
    rw [(kv _ (Or.inl (by rw [up_mk_val]; omega))).2]
    exact hin.heads _ (by rw [up_mk_val]; omega)
  · intro hm' i
    subst hσ
    exact SourceFactorSel.CoefBridge.coefT_conj pcpp coordinate ph ci T e hTL hTR heL heR m hm' b Rc A3
      (fun i => up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) o3 i
  · intro k hk h34 h35 h36
    have hA := kv (up ⟨k, by unfold NF; omega⟩) (Or.inl (by rw [up_mk_val]; exact hk))
    refine ⟨?_, hA.2⟩
    rw [kp3 _ (by rw [up_mk_val]; omega), kp2 _ (by rw [up_mk_val]; unfold NF; omega) (by rw [up_mk_val]; omega)]
    exact hA.1

theorem four_symK (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hread : CoordReads true coordinate bits) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (e : Bool → RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length)
    (L target cwid cw D K b Rc QK : Nat) (bmL bmR : List Bool)
    (hcwid : cwid = SymOriginal.symCodeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hbmL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      bmL = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      bmR = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmD : bmL.length ≤ D ∧ bmR.length ≤ D)
    (hwin : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex (pcpp.clauses ci).left).val ∨
      jj = (literalIndex (pcpp.clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : n0 + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (σ : Option Sel)
    (hσ : σ = selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m)
    (A : Fin (NF + (19 + 4 * (PS (pcpp := pcpp) da Pw W Ld).t)) → List Bool)
    (H : Fin (NF + (19 + 4 * (PS (pcpp := pcpp) da Pw W Ld).t)) → Nat)
    (hin : BackInK (PS (pcpp := pcpp) da Pw W Ld).t true A H σ ph bits n0 Pw W Ld L target cwid cw D K b
      (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val Rc bmL bmR QK) :
    ∃ (H1 : Fin (NF + (19 + 4 * (PS (pcpp := pcpp) da Pw W Ld).t)) → Nat)
      (A1 : Fin (NF + (19 + 4 * (PS (pcpp := pcpp) da Pw W Ld).t)) → List Bool),
      Step (SourceFactorSel.Slots4.fourM (slB (PS (pcpp := pcpp) da Pw W Ld) rfl))
        (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 0) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ 0)) cwid cw D + 1 +
          (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 1) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ 1)) cwid cw D + 1 +
          (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 2) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ 2)) cwid cw D + 1 +
          SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 3) then (literalIndex (pcpp.clauses ci).right).val
            else (literalIndex (pcpp.clauses ci).left).val) (fIdx (facAt σ 3)) cwid cw D))) H A H1 A1 ∧
      (∀ (i : Fin 4) (n : Fin 16),
        A1 (rgP _ (FactorLoop.cslot (PS (pcpp := pcpp) da Pw W Ld) i ((PS (pcpp := pcpp) da Pw W Ld).descSlots n))) =
          ZeroPadding.pad Rc ((PS (pcpp := pcpp) da Pw W Ld).Desc ((FactorLoop.factorsAt coordinate ph ci m)[i.val]?) n) ∧
        H1 (rgP _ (FactorLoop.cslot (PS (pcpp := pcpp) da Pw W Ld) i ((PS (pcpp := pcpp) da Pw W Ld).descSlots n))) = 0) ∧
      (∀ i : Fin 4, fTerm (facAt σ i.val) = true →
        A1 (up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩) = ZeroPadding.pad Rc
          (RepairOrdinary.CloseoutRowsEstimatorCoefficients.Product.record cw
            (SourceFactorSel.CoefBridge.tco T (facAt σ i.val)))) ∧
      (∀ i : Fin 4, H1 (up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩) = 0) ∧
      (∀ x, SourceFactorSel.Slots4.Kept (slB (PS (pcpp := pcpp) da Pw W Ld) rfl) x → A1 x = A x ∧ H1 x = H x) := by
  have hyp := fun i : Fin 4 => slot_hyps_sym coordinate bits hread ph ci T e hTL hTR heL heR m hm Ld cwid cw D Rc hcwid
    h2cw bmL bmR hbmL hbmR hbmD hwin i σ hσ
  have hRc1 : 1 ≤ Rc := by omega
  obtain ⟨cs, ct, cr, ci', ck, crho⟩ := hin.cur
  obtain ⟨H1, A1, st, hdesc, hrec, hrecH, hkept⟩ := SourceFactorSel.Slots4.sym_four (slB (PS (pcpp := pcpp) da Pw W Ld) rfl) (slB_inj (PS (pcpp := pcpp) da Pw W Ld) rfl)
    (slB_disj (PS (pcpp := pcpp) da Pw W Ld) rfl) Pw W Ld (fun i => (FactorLoop.factorsAt coordinate ph ci m)[i.val]?) bmL bmR bits
    (fun i => fSys (facAt σ i.val)) (fun i => fTerm (facAt σ i.val)) (fun i => fSide (facAt σ i.val))
    (fun i => fIdx (facAt σ i.val)) (literalIndex (pcpp.clauses ci).left).val
    (literalIndex (pcpp.clauses ci).right).val cwid cw D Rc Rc Rc Rc Rc Rc Rc Rc 0 Rc Rc H A
    (by
      intro i j
      have := i.isLt; have := j.isLt
      by_cases hj4 : j.val < 4
      · rw [slB_curvS da Pw W Ld ph i j hj4 ⟨6 + 4 * i.val + j.val, by omega⟩ rfl]
        exact hin.curH _
      apply hin.heads
      by_cases hj : 17 ≤ j.val ∧ j.val < 33
      · rw [slB_rg (PS (pcpp := pcpp) da Pw W Ld) rfl i j hj.1 hj.2, rg_val]; unfold NF; omega
      · rw [slB_lo (PS (pcpp := pcpp) da Pw W Ld) rfl i j hj]
        rcases loVal_cases i.val j.val i.isLt hj with ⟨h1, e1, -⟩ | ⟨-, e1⟩ | ⟨-, e1⟩ <;> rw [e1]
        · have := inPort_heads i.val i.isLt j.val h1 (by omega); omega
        · omega
        · omega)
    (fun i => (congrArg A (slB_curvS da Pw W Ld ph i 0 (by decide) (sysT i) (by simp [sysT]))).trans (cs i))
    (fun i => (congrArg A (slB_curvS da Pw W Ld ph i 1 (by decide) (termT i) (by simp [termT]; omega))).trans (ct i))
    (fun i => (congrArg A (slB_curvS da Pw W Ld ph i 2 (by decide) (rightT i) (by simp [rightT]; omega))).trans (cr i))
    hRc1
    (by
      intro i
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (congrArg A (slB_curvS da Pw W Ld ph i 3 (by decide) (idxT i) (by simp [idxT]; omega))).trans (ci' i)
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨4, by decide⟩) = _; rw [slB_inS da Pw W Ld i 4 (by decide) (by decide)]; exact hin.uiL
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨5, by decide⟩) = _; rw [slB_inS da Pw W Ld i 5 (by decide) (by decide)]; exact hin.uiR
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨6, by decide⟩) = _; rw [slB_inS da Pw W Ld i 6 (by decide) (by decide)]; exact hin.ubL
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨7, by decide⟩) = _; rw [slB_inS da Pw W Ld i 7 (by decide) (by decide)]; exact hin.ubR
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨8, by decide⟩) = _; rw [slB_inS da Pw W Ld i 8 (by decide) (by decide), ZeroPadding.pad_zero]
        exact hin.wit
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨9, by decide⟩) = _; rw [slB_inS da Pw W Ld i 9 (by decide) (by decide)]; exact hin.ucwid
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨10, by decide⟩) = _; rw [slB_inS da Pw W Ld i 10 (by decide) (by decide)]; exact hin.ucw
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨11, by decide⟩) = _; rw [slB_inS da Pw W Ld i 11 (by decide) (by decide)]; exact hin.tpl
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨12, by decide⟩) = _; rw [slB_inS da Pw W Ld i 12 (by decide) (by decide)]; exact hin.uP
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨13, by decide⟩) = _; rw [slB_inS da Pw W Ld i 13 (by decide) (by decide)]; exact hin.uW
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨14, by decide⟩) = _; rw [slB_inS da Pw W Ld i 14 (by decide) (by decide)]; exact hin.uL
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨15, by decide⟩) = _; rw [slB_inS da Pw W Ld i 15 (by decide) (by decide)]; exact hin.uD
      · show A (slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨16, by decide⟩) = _; rw [slB_inS da Pw W Ld i 16 (by decide) (by decide)]; exact hin.logs.1
      · intro j hj
        have := i.isLt; have := j.isLt
        by_cases hj' : j.val < 33
        · rw [slB_rg (PS (pcpp := pcpp) da Pw W Ld) rfl i j hj hj']; exact hin.region _
        · have e : slB (PS (pcpp := pcpp) da Pw W Ld) rfl i j = up ⟨loVal i.val j.val, by
              rcases loVal_cases i.val j.val i.isLt (by omega) with ⟨h1, e1, -⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1] <;>
                unfold NF <;> omega⟩ := Fin.ext (by rw [slB_lo (PS (pcpp := pcpp) da Pw W Ld) rfl i j (by omega)]; rfl)
          rw [e]
          apply hin.hi
          rcases loVal_cases i.val j.val i.isLt (by omega) with ⟨h1, e1, -⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1] <;> omega)
    hqD hPD hWD hLD hDR hDC (fun i => (hyp i).1) (fun i => (hyp i).2.1) (fun i => (hyp i).2.2.1)
    (fun i => (hyp i).2.2.2.1)
  refine ⟨H1, A1, st, ?_, ?_, ?_, hkept⟩
  · intro i n
    have e : slB (PS (pcpp := pcpp) da Pw W Ld) rfl i (SourceFactorSel.Slot.outP n) =
        rgP (PS (pcpp := pcpp) da Pw W Ld) (FactorLoop.cslot (PS (pcpp := pcpp) da Pw W Ld) i ((PS (pcpp := pcpp) da Pw W Ld).descSlots n)) := by
      rw [slB_rg (PS (pcpp := pcpp) da Pw W Ld) rfl i _ (by simp [SourceFactorSel.Slot.outP]) (by simp [SourceFactorSel.Slot.outP]; omega)]
      congr 3
      apply Fin.ext; simp [SourceFactorSel.Slot.outP]
    rw [← e]; exact hdesc i n
  · intro i ht
    obtain ⟨ts, hi, hraw, -⟩ := (hyp i).2.2.2.1 ht
    have e33 : slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨33, by decide⟩ = up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩ :=
      Fin.ext (by rw [slB_lo (PS (pcpp := pcpp) da Pw W Ld) rfl i _ (by simp), up_val]; simp [loVal])
    rw [← e33, (hyp i).2.2.2.2 ht ts hraw hi]
    exact hrec i ht ts hraw hi
  · intro i
    have e33 : slB (PS (pcpp := pcpp) da Pw W Ld) rfl i ⟨33, by decide⟩ = up ⟨1400 + i.val, by have := i.isLt; unfold NF; omega⟩ :=
      Fin.ext (by rw [slB_lo (PS (pcpp := pcpp) da Pw W Ld) rfl i _ (by simp), up_val]; simp [loVal])
    rw [← e33]; exact hrecH i

/-- **FactorSelection's back, SYM mode, value-bounded, on the packed machine `backPS`.** As PK's `SelBackSym.back_sym`, with the
coefficient window at the value bound `V` (`hV4`, `hcoefV`, `hbigR`). -/
theorem back_symK (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)
    (bits : List Bool) (hread : CoordReads true coordinate bits) (ph : Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (e : Bool → RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp)
    (hTL : T false = (coordinate (literalIndex (pcpp.clauses ci).left)).monomials)
    (hTR : T true = (coordinate (literalIndex (pcpp.clauses ci).right)).monomials)
    (heL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      e false = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).left).val, h⟩)
    (heR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      e true = RepairSource.CloseoutFinal.C10TotalDecode.Atom.systematic ⟨(literalIndex (pcpp.clauses ci).right).val, h⟩)
    (m : Nat) (hm : m ≤ (FactorLoop.monomials coordinate ph ci).length)
    (L target cwid cw D b Rc c QK : Nat) (bmL bmR : List Bool)
    (hcwid : cwid = SymOriginal.symCodeWidth Ld) (h2cw : 2 * cwid + 1 ≤ D)
    (hbmL : ∀ h : (literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits,
      bmL = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmR : ∀ h : (literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits,
      bmR = PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap (pcpp.systematicSupport ⟨_, h⟩))
    (hbmD : bmL.length ≤ D ∧ bmR.length ≤ D)
    (hwin : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (literalIndex (pcpp.clauses ci).left).val ∨
      jj = (literalIndex (pcpp.clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc)
    (hqD : n0 + 2 ≤ D) (hPD : Pw ≤ D) (hWD : W ≤ D) (hLD : Ld ≤ D) (hDR : D ≤ Rc) (hDC : D + 1 ≤ Rc)
    (hHfit : SourceFactorSel.HdrBlock.Fits true n0 L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc
      Rc Rc)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (V : Nat) (hV4 : 4 ≤ V)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < V ∧ mo.coefficient.den < V)
    (hbigR : SourceFactorSel.CoefR.coefBigR V (2 ^ pcpp.clauseBits) b (cw + rhoW) ≤ Rc)
    (σ : Option Sel)
    (hσ : σ = selAt ph (decide ((literalIndex (pcpp.clauses ci).left).val < pcpp.systematicBits))
      (decide ((literalIndex (pcpp.clauses ci).right).val < pcpp.systematicBits))
      (literalNegated (pcpp.clauses ci).left) (literalNegated (pcpp.clauses ci).right)
      (coordinate (literalIndex (pcpp.clauses ci).left)).monomials.length
      (coordinate (literalIndex (pcpp.clauses ci).right)).monomials.length m)
    (A : Fin (NF + (19 + 4 * tS)) → List Bool)
    (H : Fin (NF + (19 + 4 * tS)) → Nat)
    (hin : BackInK (SelBackSym.PS (pcpp := pcpp) da Pw W Ld).t true A H σ ph bits n0 Pw W Ld L target cwid cw D
      (2 ^ pcpp.clauseBits) b (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val Rc
      bmL bmR QK) :
    ∃ (H' : Fin (NF + (19 + 4 * tS)) → Nat) (A' : Fin (NF + (19 + 4 * tS)) → List Bool),
      Step backPS
        (SelBackSym.backSymCost T bits (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val σ
          cwid cw D n0 L target (FactorLoop.factorsAt coordinate ph ci m).length (2 ^ pcpp.clauseBits) b) H A H' A' ∧
      (∀ x, H' (rgP (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) x) = 0) ∧
      (∀ x, A' (rgP (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) x) = FactorLoop.entry (SelBackSym.PS (pcpp := pcpp) da Pw W Ld)
        (header true n0 L target (FactorLoop.factorsAt coordinate ph ci m).length)
        (fun k => (SelBackSym.PS (pcpp := pcpp) da Pw W Ld).Desc (FactorLoop.factorsAt coordinate ph ci m)[k.val]?) Rc x) ∧
      (∀ i : Fin 3, H' (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = 0) ∧
      (∀ hm' : m < (FactorLoop.monomials coordinate ph ci).length, ∀ i : Fin 3,
        A' (up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) = ZeroPadding.pad Rc (RepairOrdinary.frame
          (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
            (CloseoutFinalC10SupplierCalls.coefficientEstimate ((FactorLoop.monomials coordinate ph ci)[m]).coefficient)
            0 0 ⟨i.val, by omega⟩))) ∧
      (∀ k (hk : k < 1400), k ≠ 34 → k ≠ 35 → k ≠ 36 →
        A' (up ⟨k, by unfold NF; omega⟩) = A (up ⟨k, by unfold NF; omega⟩) ∧
        H' (up ⟨k, by unfold NF; omega⟩) = H (up ⟨k, by unfold NF; omega⟩)) := by
  obtain ⟨H1, A1, s1, hdesc, hrec, hrecH, kept1⟩ := four_symK da Pw W Ld coordinate bits hread ph ci T e hTL hTR heL heR
    m hm L target cwid cw D (2 ^ pcpp.clauseBits) b Rc QK bmL bmR hcwid h2cw hbmL hbmR hbmD hwin hqD hPD hWD hLD hDR hDC σ hσ
    A H hin
  have kv : ∀ x : Fin (NF + (19 + 4 * (SelBackSym.PS (pcpp := pcpp) da Pw W Ld).t)),
      x.val < 1400 ∨ (6000 ≤ x.val ∧ x.val < NF) → A1 x = A x ∧ H1 x = H x := by
    intro x hx
    rw [up_of x (hx.elim (fun h => Nat.lt_of_lt_of_le h (by decide)) (fun h => h.2))]
    exact kept1 _ (SelBackSym.kept_loS da Pw W Ld x.val hx)
  have rkept : ∀ x : Fin (19 + 4 * (SelBackSym.PS (pcpp := pcpp) da Pw W Ld).t),
      (∀ i n, FactorLoop.cslot (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) i ((SelBackSym.PS (pcpp := pcpp) da Pw W Ld).descSlots n) ≠ x) →
      A1 (rgP _ x) = List.replicate Rc false ∧ H1 (rgP _ x) = 0 := by
    intro x hx
    obtain ⟨a1, h1⟩ := kept1 _ (SelBackSym.kept_rgS da Pw W Ld x hx)
    exact ⟨a1.trans (hin.region x), h1.trans (hin.heads _ (by rw [rg_val]; unfold NF; omega))⟩
  have c0ne : ∀ i n, FactorLoop.cslot (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) i ((SelBackSym.PS (pcpp := pcpp) da Pw W Ld).descSlots n) ≠
      ⟨0, by omega⟩ := by
    intro i n e0
    have := FactorLoop.cslot_ge (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) i ((SelBackSym.PS (pcpp := pcpp) da Pw W Ld).descSlots n)
    rw [e0] at this; simp at this
  have hlen : (FactorLoop.factorsAt coordinate ph ci m).length = kOf σ := by
    rw [hσ]; exact SourceFactorSel.KBridge.factorsAt_len true pcpp coordinate bits hread ph ci T e hTL hTR heL heR m hm
  obtain ⟨A2, s2, o2, kp2, kp2r⟩ := hdr_stageK (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) Pw W Ld σ ph bits n0 L target cwid cw D
    (2 ^ pcpp.clauseBits) b (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val Rc c QK
    bmL bmR A A1 H H1 hin kv (rkept _ c0ne) _ hlen hHfit
  have hT : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw := by
    intro r mo hmo
    cases r with
    | false => rw [hTL] at hmo; exact hcoef _ mo hmo
    | true => rw [hTR] at hmo; exact hcoef _ mo hmo
  have hTV : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < V ∧ mo.coefficient.den < V := by
    intro r mo hmo
    cases r with
    | false => rw [hTL] at hmo; exact hcoefV _ mo hmo
    | true => rw [hTR] at hmo; exact hcoefV _ mo hmo
  have hrb : (rhoOf σ).num.natAbs < 2 ^ rhoW ∧ (rhoOf σ).den < 2 ^ rhoW := by
    rw [hσ]; exact SelRho.rho_bits _ _ _ _ _ _ _ _
  obtain ⟨A3, s3, o3, kp3⟩ := coef_stageK (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) Pw W Ld σ ph bits n0 L target cwid cw D
    (2 ^ pcpp.clauseBits) b (literalIndex (pcpp.clauses ci).left).val (literalIndex (pcpp.clauses ci).right).val Rc QK
    bmL bmR T A A1 A2 H H1 hin kv hrec hrecH kp2 hcw1 hT V hV4 hTV hrb (Nat.two_pow_pos _) hbigR
  have st := (four_packedS pcpp da Pw W Ld _ H H1 A A1 s1).seq
    ((hdr_packedS pcpp da Pw W Ld _ H1 H1 A1 A2 s2).seq (coef_packedS pcpp da Pw W Ld _ H1 H1 A2 A3 s3))
  refine ⟨H1, A3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SelBackSym.backSymCost SelBackSym.fourCostS
    exact st
  · intro x
    by_cases hx : ∃ i n, FactorLoop.cslot (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) i ((SelBackSym.PS (pcpp := pcpp) da Pw W Ld).descSlots n) = x
    · obtain ⟨i, n, rfl⟩ := hx
      exact (hdesc i n).2
    · exact (rkept x (fun i n e => hx ⟨i, n, e⟩)).2
  · apply SourceFactorSel.Modes.entry_of_ports (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) (rgP _)
    · rw [kp3 _ (Or.inr (Or.inr (by rw [rg_val]; omega)))]; exact o2
    · intro i n
      rw [kp3 _ (Or.inr (Or.inr (by rw [rg_val]; omega))),
        kp2r _ (by have := FactorLoop.cslot_ge (SelBackSym.PS (pcpp := pcpp) da Pw W Ld) i ((SelBackSym.PS (pcpp := pcpp) da Pw W Ld).descSlots n); omega)]
      exact (hdesc i n).1
    · intro x hx0 hx
      rw [kp3 _ (Or.inr (Or.inr (by rw [rg_val]; omega))), kp2r _ hx0]
      exact (rkept x hx).1
  · intro i
    have := i.isLt
    rw [(kv _ (Or.inl (by rw [up_mk_val]; omega))).2]
    exact hin.heads _ (by rw [up_mk_val]; omega)
  · intro hm' i
    subst hσ
    exact SourceFactorSel.CoefBridge.coefT_conj pcpp coordinate ph ci T e hTL hTR heL heR m hm' b Rc A3
      (fun i => up ⟨34 + i.val, by have := i.isLt; unfold NF; omega⟩) o3 i
  · intro k hk h34 h35 h36
    have hA := kv (up ⟨k, by unfold NF; omega⟩) (Or.inl (by rw [up_mk_val]; exact hk))
    refine ⟨?_, hA.2⟩
    rw [kp3 _ (by rw [up_mk_val]; omega), kp2 _ (by rw [up_mk_val]; unfold NF; omega) (by rw [up_mk_val]; omega)]
    exact hA.1

end

end
end NearCubicWires.SourceRequest.SelLocal

