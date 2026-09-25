import Proof.Rows.RowsMaskGeneric
import Proof.Rows.RowsSymVerdict

/-! # Rows C3: the selection mask of one row, both modes, through ONE loop design

**Consumer.** Warm field 2 of the row's `datumFields`: `gridWord live s harity row.select`, where
`row.select` is `Packets.symFamily`'s (`decide (symOffsets r I (joinInput I (fun _ => false) z) = offset)`)
or `Packets.thrFamily`'s (`decide (modularOffset occ I (joinInput …) (equation a r sel) p = o)`)
(`fixed-live-packet-parent-20260921/PCJ9eff70d512234a4c_Packets.lean:62,74`).

Both are instances of `RowsMaskGeneric.gmask` (one fixed loop machine per mode, the verdict machine the
only difference): THR with `ThresholdTraversal.machine` (verdict port by `StreamCompare.output_verdict`),
SYM with `RowsSymVerdict.machine`. **Paper / budget:** `paper.tex:1190-1212`, table class (`2^s` cells ×
per-cell poly in the request).
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ModeMasks
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.BlockPlatform RowsConstruction.ThrCell RowsConstruction.ThrMask
open RowsConstruction.MaskGeneric
noncomputable section

/-! ## THR -/

section THR
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q))
  {cutoff : Nat} (prime : PrimeIndex cutoff) (o : Fin prime.val) (T L target w F U v C P : Nat)

theorem thr_run (x : BitInput r.q)
    (hnative : (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ T)
    (hb : PCJ45bee56da9f34d5a_FourfoldPowerData.Bounds (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
      (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val w F U v C P)
    (hQ : (PCJ45bee56da9f34d5a_StreamPair.flags r I x).length+1 ≤ U)
    (hcs : (PCJ45bee56da9f34d5a_StreamPairPorts.coefficientWord (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
      (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val w o.val).length ≤ U)
    (hs : (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ U) :
    ∃ J B, Step PCJ45bee56da9f34d5a_ThresholdTraversal.machine
        (PCJ45bee56da9f34d5a_ThresholdTraversal.budget a r sel I x T L target w U P)
        PCJ45bee56da9f34d5a_ThresholdTraversal.initialHeads
        (PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v) J B ∧
      J 253 = 0 ∧ readTapeBit (B 253) 0 = PCJ45bee56da9f34d5a_StreamCompare.verdict a r sel I x prime o := by
  refine ⟨_, _, PCJ45bee56da9f34d5a_ThresholdTraversal.run a r four sel I x prime o T L target w F U v C P
    hnative hb hQ hcs hs, PCJ45bee56da9f34d5a_StreamCompare.output_verdict_head a r four sel I x prime o L target w, ?_⟩
  rw [PCJ45bee56da9f34d5a_StreamCompare.output_verdict]
  rfl

/-- **THR mask through the generic loop.** -/
theorem thr_gmask (s : Nat) (ha : (s+1)/2+s/2=Iᶜ.card) (R Cl Dl Bt : Nat) (M : Fin 254 → List Bool)
    (hnative : (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ T)
    (hb : PCJ45bee56da9f34d5a_FourfoldPowerData.Bounds (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
      (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val w F U v C P)
    (hcs : (PCJ45bee56da9f34d5a_StreamPairPorts.coefficientWord (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
      (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val w o.val).length ≤ U)
    (hs : (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ U)
    (hQ : ∀ x : BitInput r.q, (PCJ45bee56da9f34d5a_StreamPair.flags r I x).length+1 ≤ U)
    (hbt : ∀ x : BitInput r.q, PCJ45bee56da9f34d5a_ThresholdTraversal.budget a r sel I x T L target w U P ≤ Bt)
    (hBt : Bt+2 ≤ R) (hm109 : M 109 = List.replicate R false) (hml : ∀ i, (M i).length ≤ R)
    (hmne : ∀ (x : BitInput r.q) (i : Fin 254), i ≠ 109 → ZeroPadding.pad R (M i) =
      ZeroPadding.pad R (PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v i))
    (hqR : r.q ≤ R) (hsR : (s+1)/2+s/2 ≤ R) (hcl : 2*((s+1)/2)+1 ≤ Cl) (hcr : 2*(s/2)+1 ≤ Cl)
    (hdl : 4*((s+1)/2+s/2)+7 ≤ Dl) (hdq : 4*r.q+3 ≤ Dl) (hdi : 2*((s+1)/2)+1 ≤ Dl) (out : List Bool) :
    Step (CloseoutRowsDegreeLoop.machine (gouterBody PCJ45bee56da9f34d5a_ThresholdTraversal.machine
        PCJ45bee56da9f34d5a_ThresholdTraversal.initialHeads)) (2^((s+1)/2)*(rowCost s r.q R Bt+3)+3)
      (Fin.addCases (Fin.addCases (heads out.length) (fun _ : Fin 1 => 1)) (fun _ : Fin 1 => 1))
      (Fin.addCases (Fin.addCases (tapes I s R Cl Dl 0 0 M out)
        (fun _ : Fin 1 => CompareMachine.word (2^(s/2))))
        (fun _ : Fin 1 => CompareMachine.word (2^((s+1)/2))))
      (Fin.addCases (Fin.addCases (heads (out ++ PCJ45bee56da9f34d5a_SelectionWord.gridWord I s ha
        (fun z => decide (PCJ9eff70d512234a4c_Fixed.LiveRows.modularOffset (thresholdFourfoldOccurrences r) I
          (C10SupplierRowInput.joinInput I (fun _ => false) z) (ThresholdRows.equation a r sel)
          prime.val = o.val))).length) (fun _ : Fin 1 => 1)) (fun _ : Fin 1 => 1))
      (Fin.addCases (Fin.addCases (tapes I s R Cl Dl 0 0 M (out ++
        PCJ45bee56da9f34d5a_SelectionWord.gridWord I s ha
          (fun z => decide (PCJ9eff70d512234a4c_Fixed.LiveRows.modularOffset (thresholdFourfoldOccurrences r) I
            (C10SupplierRowInput.joinInput I (fun _ => false) z) (ThresholdRows.equation a r sel)
            prime.val = o.val))))
        (fun _ : Fin 1 => CompareMachine.word (2^(s/2))))
        (fun _ : Fin 1 => CompareMachine.word (2^((s+1)/2)))) := by
  have h : Premises PCJ45bee56da9f34d5a_ThresholdTraversal.machine PCJ45bee56da9f34d5a_ThresholdTraversal.initialHeads
      (fun x => PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v)
      (fun x => PCJ45bee56da9f34d5a_StreamCompare.verdict a r sel I x prime o)
      (fun x => PCJ45bee56da9f34d5a_ThresholdTraversal.budget a r sel I x T L target w U P)
      I s R Cl Dl Bt M :=
    { hle := PCJ45bee56da9f34d5a_ThresholdTraversal.initialHeads_le
      run := fun x => thr_run a r four sel I prime o T L target w F U v C P x hnative hb (hQ x) hcs hs
      m109 := hm109
      mlen := hml
      mne := hmne
      in109 := fun x => CellInput.input_109 a r four sel I prime o T L target w F U v x
      qR := hqR
      sR := hsR
      cl := hcl
      cr := hcr
      dl := hdl
      dq := hdq
      di := hdi
      n := hbt
      nt := hBt }
  exact gmask h ha out
end THR

/-! ## SYM -/

section SYM
variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)

theorem sym_input_x (I : Finset (Fin r.q)) (x x' : BitInput r.q) (L target T w Dc cap : Nat)
    (offset : Fin r.circuits.length → Nat) :
    SymVerdict.input r I x L target T w Dc cap offset =
      Function.update (SymVerdict.input r I x' L target T w Dc cap offset) 109 (List.ofFn x) := by
  unfold SymVerdict.input SymVerdict.symLayout PCJ45bee56da9f34d5a_NativeFamilyCount.bank
    PCJ45bee56da9f34d5a_CircuitFlagBank.bank PCJ45bee56da9f34d5a_NativeCircuitCount.bank
    PCJ45bee56da9f34d5a_CountedGateCell.bank PCJ45bee56da9f34d5a_FramedGateBank.bank
    PCJ45bee56da9f34d5a_FramedGateBank.coreBank
  rw [CellInput.extra_x I x x']
  simp only [CellInput.addCases_update_left, CellInput.addCases_update_right]
  rfl

theorem sym_input_109 (I : Finset (Fin r.q)) (x : BitInput r.q) (L target T w Dc cap : Nat)
    (offset : Fin r.circuits.length → Nat) :
    SymVerdict.input r I x L target T w Dc cap offset 109 = List.ofFn x := by
  rw [sym_input_x r I x x L target T w Dc cap offset, Function.update_self]

theorem heads0_le : ∀ i, SymVerdict.heads0 i ≤ 1 := by
  intro i
  unfold SymVerdict.heads0 SymVerdict.symLayout
  refine Fin.addCases (m:=128) (n:=126) (fun f => ?_) (fun y => ?_) i
  · simp only [Fin.addCases_left]
    exact (by decide : ∀ f : Fin 128, PCJ45bee56da9f34d5a_NativeFamilyCount.heads 0 [] 0 0 f ≤ 1) f
  · simp only [Fin.addCases_right]
    refine Fin.addCases (m:=18) (n:=108) (fun k => ?_) (fun z => ?_) y
    · simp only [Fin.addCases_left]
      exact (by decide : ∀ k : Fin 18, SymVerdict.auxHeads0 k ≤ 1) k
    · simp only [Fin.addCases_right]
      refine Fin.addCases (m:=107) (n:=1) (fun _ => ?_) (fun _ => ?_) z <;>
        simp only [Fin.addCases_left, Fin.addCases_right, Nat.zero_le]

/-- **SYM mask through the generic loop.** Appends exactly `Packets.symFamily`'s selection word. -/
theorem sym_gmask (four : r.circuits.length ≤ 4) (I : Finset (Fin r.q)) (L target T w Dc cap : Nat)
    (offset : Fin r.circuits.length → Nat) (s : Nat) (ha : (s+1)/2+s/2=Iᶜ.card) (R Cl Dl : Nat)
    (M : Fin 254 → List Bool)
    (hb : (SymVerdict.src r L target).length ≤ T) (hw4 : 4 < 2^w) (hN : ∀ c : Fin 4, SymVerdict.N r c < 2^w)
    (hT : ∀ c : Fin 4, SymVerdict.Tg r offset c < 2^w) (hD : 2*w+1 ≤ Dc)
    (hcap1 : PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 0 r.q L target (SymMeaning.circuits r).length T ≤ cap)
    (hcapN : ∀ c : Fin 4, PCJ45bee56da9f34d5a_CountFlags.budget (SymVerdict.N r c) w ≤ cap)
    (hcap3 : (2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))) ≤ cap)
    (hcap4 : PCJ45bee56da9f34d5a_CountFlags.budget 4 w ≤ cap)
    (hcost : SymVerdict.cost r L target T w+2 ≤ R) (hm109 : M 109 = List.replicate R false)
    (hml : ∀ i, (M i).length ≤ R)
    (hmne : ∀ (x : BitInput r.q) (i : Fin 254), i ≠ 109 → ZeroPadding.pad R (M i) =
      ZeroPadding.pad R (SymVerdict.input r I x L target T w Dc cap offset i))
    (hqR : r.q ≤ R) (hsR : (s+1)/2+s/2 ≤ R) (hcl : 2*((s+1)/2)+1 ≤ Cl) (hcr : 2*(s/2)+1 ≤ Cl)
    (hdl : 4*((s+1)/2+s/2)+7 ≤ Dl) (hdq : 4*r.q+3 ≤ Dl) (hdi : 2*((s+1)/2)+1 ≤ Dl) (out : List Bool) :
    Step (CloseoutRowsDegreeLoop.machine (gouterBody SymVerdict.machine SymVerdict.heads0))
      (2^((s+1)/2)*(rowCost s r.q R (SymVerdict.cost r L target T w)+3)+3)
      (Fin.addCases (Fin.addCases (heads out.length) (fun _ : Fin 1 => 1)) (fun _ : Fin 1 => 1))
      (Fin.addCases (Fin.addCases (tapes I s R Cl Dl 0 0 M out)
        (fun _ : Fin 1 => CompareMachine.word (2^(s/2))))
        (fun _ : Fin 1 => CompareMachine.word (2^((s+1)/2))))
      (Fin.addCases (Fin.addCases (heads (out ++ PCJ45bee56da9f34d5a_SelectionWord.gridWord I s ha
        (fun z => decide (PCJ9eff70d512234a4c_Fixed.LiveRows.symOffsets r I
          (C10SupplierRowInput.joinInput I (fun _ => false) z) = offset))).length)
        (fun _ : Fin 1 => 1)) (fun _ : Fin 1 => 1))
      (Fin.addCases (Fin.addCases (tapes I s R Cl Dl 0 0 M (out ++
        PCJ45bee56da9f34d5a_SelectionWord.gridWord I s ha
          (fun z => decide (PCJ9eff70d512234a4c_Fixed.LiveRows.symOffsets r I
            (C10SupplierRowInput.joinInput I (fun _ => false) z) = offset))))
        (fun _ : Fin 1 => CompareMachine.word (2^(s/2))))
        (fun _ : Fin 1 => CompareMachine.word (2^((s+1)/2)))) := by
  have h : Premises SymVerdict.machine SymVerdict.heads0
      (fun x => SymVerdict.input r I x L target T w Dc cap offset)
      (fun x => decide (PCJ9eff70d512234a4c_Fixed.LiveRows.symOffsets r I x = offset))
      (fun _ => SymVerdict.cost r L target T w) I s R Cl Dl (SymVerdict.cost r L target T w) M :=
    { hle := heads0_le
      run := fun x => by
        obtain ⟨J, B, h1, h2, h3⟩ := SymVerdict.run r four I x L target T w Dc cap offset hb hw4 hN hT hD
          hcap1 hcapN hcap3 hcap4
        exact ⟨J, B, h1, h2, h3⟩
      m109 := hm109
      mlen := hml
      mne := hmne
      in109 := fun x => sym_input_109 r I x L target T w Dc cap offset
      qR := hqR
      sR := hsR
      cl := hcl
      cr := hcr
      dl := hdl
      dq := hdq
      di := hdi
      n := fun _ => le_refl _
      nt := hcost }
  exact gmask h ha out
end SYM

end
end RowsConstruction.ModeMasks
