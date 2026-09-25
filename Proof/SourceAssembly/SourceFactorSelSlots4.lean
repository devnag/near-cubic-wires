import Proof.SourceAssembly.SourceFactorSelSlotDock

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Slots4
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceFactorSel.Slot NearCubicWires.SourceFactorSel.SlotDock NearCubicWires.SourceRequest.TermReader
noncomputable section

/-- **The four slot pipelines** (ONE fixed machine given the four docks). -/
def fourM {U : Nat} (sl : Fin 4 → Fin 1121 → Fin U) :=
  Composition.machine (RecoveryFocus.machine (sl 0) slotM)
  (Composition.machine (RecoveryFocus.machine (sl 1) slotM)
  (Composition.machine (RecoveryFocus.machine (sl 2) slotM) (RecoveryFocus.machine (sl 3) slotM)))

/-- Ports no slot may write: outside every slot's writable part. -/
def Kept {U : Nat} (sl : Fin 4 → Fin 1121 → Fin U) (x : Fin U) : Prop := ∀ (i : Fin 4) (j : Fin 1121), sl i j = x → j.val < 17

/-- Every port of slot `i'` is kept by slot `i ≠ i'`'s run. -/
theorem other_kept {U : Nat} (sl : Fin 4 → Fin 1121 → Fin U)
    (hdisj : ∀ (i i' : Fin 4) (j j' : Fin 1121), i ≠ i' → 17 ≤ j.val → sl i j ≠ sl i' j')
    (i i' : Fin 4) (h : i ≠ i') (j' : Fin 1121) : ∀ j, sl i j = sl i' j' → j.val < 17 := by
  intro j e
  by_contra hc
  exact hdisj i i' j j' h (by omega) e

section
open RepairRepresentation SupplierPipeline SourceInterfaces SupplierEstimator NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceRequest
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)

/-- **THR mode: the four slots in sequence.** -/
theorem thr_four {U : Nat} (sl : Fin 4 → Fin 1121 → Fin U) (hsl : ∀ i, Function.Injective (sl i))
    (hdisj : ∀ (i i' : Fin 4) (j j' : Fin 1121), i ≠ i' → 17 ≤ j.val → sl i j ≠ sl i' j')
    (P W L : Nat) (o : Fin 4 → Option (C10TotalDecode.Atom pcpp)) (bmL bmR wbits : List Bool)
    (s t r : Fin 4 → Bool) (idx : Fin 4 → Nat) (iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ i j, H (sl i j) = 0)
    (h0 : ∀ i, A (sl i 0) = ZeroPadding.pad Qf [s i]) (h1 : ∀ i, A (sl i 1) = ZeroPadding.pad Qf [t i])
    (h2 : ∀ i, A (sl i 2) = ZeroPadding.pad Qf [r i]) (hQf : 1 ≤ Qf)
    (hin : ∀ i, Ins (fun j => A (sl i j)) (UnaryTemplate.tape q) (List.replicate P true) (List.replicate W true)
      (List.replicate L true) bmL bmR wbits (idx i) iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hq : q + 2 ≤ D) (hP : P ≤ D) (hW : W ≤ D) (hL : L ≤ D) (hDR : D ≤ R) (hDC : D + 1 ≤ C)
    (hk : ∀ i, kindOf false (o i) = if s i then .sys else if t i then .orig else .absent)
    (hst : ∀ i, ¬ (s i = true ∧ t i = true))
    (hbm : ∀ i, s i = true → bmOf (o i) = (if r i then bmR else bmL) ∧ (bmOf (o i)).length ≤ D)
    (hterm : ∀ i, t i = true → TermOK wbits (bitsOf false L (o i)) (if r i then iR else iL) (idx i) cwid cw D R C) :
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step (fourM sl) (slotCost wbits (if r 0 then iR else iL) (idx 0) cwid cw D + 1 +
        (slotCost wbits (if r 1 then iR else iL) (idx 1) cwid cw D + 1 +
        (slotCost wbits (if r 2 then iR else iL) (idx 2) cwid cw D + 1 +
        slotCost wbits (if r 3 then iR else iL) (idx 3) cwid cw D))) H A H' A' ∧
      (∀ (i : Fin 4) (n : Fin 16), A' (sl i (outP n)) = ZeroPadding.pad R (ThrSwitch.descAt P W L (o i) n.val) ∧
        H' (sl i (outP n)) = 0) ∧
      (∀ i : Fin 4, t i = true → ∀ ts, rawTerms wbits (if r i then iR else iL) = some ts → ∀ hi : idx i < ts.length,
        A' (sl i 33) = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx i].1)) ∧
      (∀ i : Fin 4, H' (sl i 33) = 0) ∧
      (∀ x, Kept sl x → A' x = A x ∧ H' x = H x) := by
  -- a slot's run from any bank that still agrees with `A`/`H` on the slot's own ports
  have run : ∀ (i : Fin 4) (H0 : Fin U → Nat) (A0 : Fin U → List Bool),
      (∀ j, A0 (sl i j) = A (sl i j) ∧ H0 (sl i j) = H (sl i j)) →
      ∃ (H1 : Fin U → Nat) (A1 : Fin U → List Bool),
        Step (RecoveryFocus.machine (sl i) slotM) (slotCost wbits (if r i then iR else iL) (idx i) cwid cw D) H0 A0 H1 A1 ∧
        (∀ n : Fin 16, A1 (sl i (outP n)) = ZeroPadding.pad R (ThrSwitch.descAt P W L (o i) n.val) ∧
          H1 (sl i (outP n)) = 0) ∧
        (t i = true → ∀ ts, rawTerms wbits (if r i then iR else iL) = some ts → ∀ hi : idx i < ts.length,
          A1 (sl i 33) = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx i].1)) ∧
        H1 (sl i 33) = 0 ∧
        (∀ x, (∀ j : Fin 1121, sl i j = x → j.val < 17) → A1 x = A0 x ∧ H1 x = H0 x) := by
    intro i H0 A0 hag
    have hin' : Ins (fun j => A0 (sl i j)) (UnaryTemplate.tape q) (List.replicate P true) (List.replicate W true)
        (List.replicate L true) bmL bmR wbits (idx i) iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C := by
      have e : (fun j => A0 (sl i j)) = (fun j => A (sl i j)) := funext fun j => (hag j).1
      rw [e]; exact hin i
    exact thr_slot_step (sl i) (hsl i) P W L (o i) bmL bmR wbits (s i) (t i) (r i) (idx i) iL iR cwid cw D Qf Qi Qb Qt
      Qp Qw Ql Qd Rw R C H0 A0 (fun j => (hag j).2.trans (hH i j)) ((hag 0).1.trans (h0 i)) ((hag 1).1.trans (h1 i))
      ((hag 2).1.trans (h2 i)) hQf hin' hq hP hW hL hDR hDC (hk i) (hst i) (hbm i) (hterm i)
  obtain ⟨H1, A1, s0, o0, c0, hc0, f0⟩ := run 0 H A (fun j => ⟨rfl, rfl⟩)
  obtain ⟨H2, A2, s1, o1, c1, hc1, f1⟩ := run 1 H1 A1 (fun j => f0 _ (other_kept sl hdisj 0 1 (by decide) j))
  obtain ⟨H3, A3, s2, o2, c2, hc2, f2⟩ := run 2 H2 A2 (fun j =>
    have a := f1 _ (other_kept sl hdisj 1 2 (by decide) j)
    have b := f0 _ (other_kept sl hdisj 0 2 (by decide) j)
    ⟨a.1.trans b.1, a.2.trans b.2⟩)
  obtain ⟨H4, A4, s3, o3, c3, hc3, f3⟩ := run 3 H3 A3 (fun j =>
    have a := f2 _ (other_kept sl hdisj 2 3 (by decide) j)
    have b := f1 _ (other_kept sl hdisj 1 3 (by decide) j)
    have c := f0 _ (other_kept sl hdisj 0 3 (by decide) j)
    ⟨a.1.trans (b.1.trans c.1), a.2.trans (b.2.trans c.2)⟩)
  -- a written port of slot `i` is kept by every other slot
  have keepOut : ∀ (i i' : Fin 4), i ≠ i' → ∀ j : Fin 1121, 17 ≤ j.val → ∀ j', sl i' j' = sl i j → j'.val < 17 := by
    intro i i' h j hj j' e
    by_contra hc
    exact hdisj i' i j' j (Ne.symm h) (by omega) e
  refine ⟨H4, A4, s0.seq (s1.seq (s2.seq s3)), ?_, ?_, ?_, ?_⟩
  · intro i n
    have hn : 17 ≤ (outP n).val := by simp [outP]
    fin_cases i
    · have a3 := f3 _ (keepOut 0 3 (by decide) _ hn)
      have a2 := f2 _ (keepOut 0 2 (by decide) _ hn)
      have a1 := f1 _ (keepOut 0 1 (by decide) _ hn)
      exact ⟨a3.1.trans (a2.1.trans (a1.1.trans (o0 n).1)), a3.2.trans (a2.2.trans (a1.2.trans (o0 n).2))⟩
    · have a3 := f3 _ (keepOut 1 3 (by decide) _ hn)
      have a2 := f2 _ (keepOut 1 2 (by decide) _ hn)
      exact ⟨a3.1.trans (a2.1.trans (o1 n).1), a3.2.trans (a2.2.trans (o1 n).2)⟩
    · have a3 := f3 _ (keepOut 2 3 (by decide) _ hn)
      exact ⟨a3.1.trans (o2 n).1, a3.2.trans (o2 n).2⟩
    · exact o3 n
  · intro i ht ts hr hi
    have hn : 17 ≤ (33 : Fin 1121).val := by decide
    fin_cases i
    · exact (f3 _ (keepOut 0 3 (by decide) _ hn)).1.trans ((f2 _ (keepOut 0 2 (by decide) _ hn)).1.trans
        ((f1 _ (keepOut 0 1 (by decide) _ hn)).1.trans (c0 ht ts hr hi)))
    · exact (f3 _ (keepOut 1 3 (by decide) _ hn)).1.trans ((f2 _ (keepOut 1 2 (by decide) _ hn)).1.trans
        (c1 ht ts hr hi))
    · exact (f3 _ (keepOut 2 3 (by decide) _ hn)).1.trans (c2 ht ts hr hi)
    · exact c3 ht ts hr hi
  · intro i
    have hn : 17 ≤ (33 : Fin 1121).val := by decide
    fin_cases i
    · exact (f3 _ (keepOut 0 3 (by decide) _ hn)).2.trans ((f2 _ (keepOut 0 2 (by decide) _ hn)).2.trans
        ((f1 _ (keepOut 0 1 (by decide) _ hn)).2.trans hc0))
    · exact (f3 _ (keepOut 1 3 (by decide) _ hn)).2.trans ((f2 _ (keepOut 1 2 (by decide) _ hn)).2.trans hc1)
    · exact (f3 _ (keepOut 2 3 (by decide) _ hn)).2.trans hc2
    · exact hc3
  · intro x hx
    have a3 := f3 x (hx 3)
    have a2 := f2 x (hx 2)
    have a1 := f1 x (hx 1)
    have a0 := f0 x (hx 0)
    exact ⟨a3.1.trans (a2.1.trans (a1.1.trans a0.1)), a3.2.trans (a2.2.trans (a1.2.trans a0.2))⟩

/-- **SYM mode: the four slots in sequence.** -/
theorem sym_four {U : Nat} (sl : Fin 4 → Fin 1121 → Fin U) (hsl : ∀ i, Function.Injective (sl i))
    (hdisj : ∀ (i i' : Fin 4) (j j' : Fin 1121), i ≠ i' → 17 ≤ j.val → sl i j ≠ sl i' j')
    (P W L : Nat) (o : Fin 4 → Option (C10TotalDecode.Atom pcpp)) (bmL bmR wbits : List Bool)
    (s t r : Fin 4 → Bool) (idx : Fin 4 → Nat) (iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ i j, H (sl i j) = 0)
    (h0 : ∀ i, A (sl i 0) = ZeroPadding.pad Qf [s i]) (h1 : ∀ i, A (sl i 1) = ZeroPadding.pad Qf [t i])
    (h2 : ∀ i, A (sl i 2) = ZeroPadding.pad Qf [r i]) (hQf : 1 ≤ Qf)
    (hin : ∀ i, Ins (fun j => A (sl i j)) (UnaryTemplate.tape q) (List.replicate P true) (List.replicate W true)
      (List.replicate L true) bmL bmR wbits (idx i) iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hq : q + 2 ≤ D) (hP : P ≤ D) (hW : W ≤ D) (hL : L ≤ D) (hDR : D ≤ R) (hDC : D + 1 ≤ C)
    (hk : ∀ i, kindOf true (o i) = if s i then .sys else if t i then .orig else .absent)
    (hst : ∀ i, ¬ (s i = true ∧ t i = true))
    (hbm : ∀ i, s i = true → bmOf (o i) = (if r i then bmR else bmL) ∧ (bmOf (o i)).length ≤ D)
    (hterm : ∀ i, t i = true → TermOK wbits (bitsOf true L (o i)) (if r i then iR else iL) (idx i) cwid cw D R C) :
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step (fourM sl) (slotCost wbits (if r 0 then iR else iL) (idx 0) cwid cw D + 1 +
        (slotCost wbits (if r 1 then iR else iL) (idx 1) cwid cw D + 1 +
        (slotCost wbits (if r 2 then iR else iL) (idx 2) cwid cw D + 1 +
        slotCost wbits (if r 3 then iR else iL) (idx 3) cwid cw D))) H A H' A' ∧
      (∀ (i : Fin 4) (n : Fin 16), A' (sl i (outP n)) = ZeroPadding.pad R (SymSwitch.descAt P W L (o i) n.val) ∧
        H' (sl i (outP n)) = 0) ∧
      (∀ i : Fin 4, t i = true → ∀ ts, rawTerms wbits (if r i then iR else iL) = some ts → ∀ hi : idx i < ts.length,
        A' (sl i 33) = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx i].1)) ∧
      (∀ i : Fin 4, H' (sl i 33) = 0) ∧
      (∀ x, Kept sl x → A' x = A x ∧ H' x = H x) := by
  -- a slot's run from any bank that still agrees with `A`/`H` on the slot's own ports
  have run : ∀ (i : Fin 4) (H0 : Fin U → Nat) (A0 : Fin U → List Bool),
      (∀ j, A0 (sl i j) = A (sl i j) ∧ H0 (sl i j) = H (sl i j)) →
      ∃ (H1 : Fin U → Nat) (A1 : Fin U → List Bool),
        Step (RecoveryFocus.machine (sl i) slotM) (slotCost wbits (if r i then iR else iL) (idx i) cwid cw D) H0 A0 H1 A1 ∧
        (∀ n : Fin 16, A1 (sl i (outP n)) = ZeroPadding.pad R (SymSwitch.descAt P W L (o i) n.val) ∧
          H1 (sl i (outP n)) = 0) ∧
        (t i = true → ∀ ts, rawTerms wbits (if r i then iR else iL) = some ts → ∀ hi : idx i < ts.length,
          A1 (sl i 33) = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx i].1)) ∧
        H1 (sl i 33) = 0 ∧
        (∀ x, (∀ j : Fin 1121, sl i j = x → j.val < 17) → A1 x = A0 x ∧ H1 x = H0 x) := by
    intro i H0 A0 hag
    have hin' : Ins (fun j => A0 (sl i j)) (UnaryTemplate.tape q) (List.replicate P true) (List.replicate W true)
        (List.replicate L true) bmL bmR wbits (idx i) iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C := by
      have e : (fun j => A0 (sl i j)) = (fun j => A (sl i j)) := funext fun j => (hag j).1
      rw [e]; exact hin i
    exact sym_slot_step (sl i) (hsl i) P W L (o i) bmL bmR wbits (s i) (t i) (r i) (idx i) iL iR cwid cw D Qf Qi Qb Qt
      Qp Qw Ql Qd Rw R C H0 A0 (fun j => (hag j).2.trans (hH i j)) ((hag 0).1.trans (h0 i)) ((hag 1).1.trans (h1 i))
      ((hag 2).1.trans (h2 i)) hQf hin' hq hP hW hL hDR hDC (hk i) (hst i) (hbm i) (hterm i)
  obtain ⟨H1, A1, s0, o0, c0, hc0, f0⟩ := run 0 H A (fun j => ⟨rfl, rfl⟩)
  obtain ⟨H2, A2, s1, o1, c1, hc1, f1⟩ := run 1 H1 A1 (fun j => f0 _ (other_kept sl hdisj 0 1 (by decide) j))
  obtain ⟨H3, A3, s2, o2, c2, hc2, f2⟩ := run 2 H2 A2 (fun j =>
    have a := f1 _ (other_kept sl hdisj 1 2 (by decide) j)
    have b := f0 _ (other_kept sl hdisj 0 2 (by decide) j)
    ⟨a.1.trans b.1, a.2.trans b.2⟩)
  obtain ⟨H4, A4, s3, o3, c3, hc3, f3⟩ := run 3 H3 A3 (fun j =>
    have a := f2 _ (other_kept sl hdisj 2 3 (by decide) j)
    have b := f1 _ (other_kept sl hdisj 1 3 (by decide) j)
    have c := f0 _ (other_kept sl hdisj 0 3 (by decide) j)
    ⟨a.1.trans (b.1.trans c.1), a.2.trans (b.2.trans c.2)⟩)
  -- a written port of slot `i` is kept by every other slot
  have keepOut : ∀ (i i' : Fin 4), i ≠ i' → ∀ j : Fin 1121, 17 ≤ j.val → ∀ j', sl i' j' = sl i j → j'.val < 17 := by
    intro i i' h j hj j' e
    by_contra hc
    exact hdisj i' i j' j (Ne.symm h) (by omega) e
  refine ⟨H4, A4, s0.seq (s1.seq (s2.seq s3)), ?_, ?_, ?_, ?_⟩
  · intro i n
    have hn : 17 ≤ (outP n).val := by simp [outP]
    fin_cases i
    · have a3 := f3 _ (keepOut 0 3 (by decide) _ hn)
      have a2 := f2 _ (keepOut 0 2 (by decide) _ hn)
      have a1 := f1 _ (keepOut 0 1 (by decide) _ hn)
      exact ⟨a3.1.trans (a2.1.trans (a1.1.trans (o0 n).1)), a3.2.trans (a2.2.trans (a1.2.trans (o0 n).2))⟩
    · have a3 := f3 _ (keepOut 1 3 (by decide) _ hn)
      have a2 := f2 _ (keepOut 1 2 (by decide) _ hn)
      exact ⟨a3.1.trans (a2.1.trans (o1 n).1), a3.2.trans (a2.2.trans (o1 n).2)⟩
    · have a3 := f3 _ (keepOut 2 3 (by decide) _ hn)
      exact ⟨a3.1.trans (o2 n).1, a3.2.trans (o2 n).2⟩
    · exact o3 n
  · intro i ht ts hr hi
    have hn : 17 ≤ (33 : Fin 1121).val := by decide
    fin_cases i
    · exact (f3 _ (keepOut 0 3 (by decide) _ hn)).1.trans ((f2 _ (keepOut 0 2 (by decide) _ hn)).1.trans
        ((f1 _ (keepOut 0 1 (by decide) _ hn)).1.trans (c0 ht ts hr hi)))
    · exact (f3 _ (keepOut 1 3 (by decide) _ hn)).1.trans ((f2 _ (keepOut 1 2 (by decide) _ hn)).1.trans
        (c1 ht ts hr hi))
    · exact (f3 _ (keepOut 2 3 (by decide) _ hn)).1.trans (c2 ht ts hr hi)
    · exact c3 ht ts hr hi
  · intro i
    have hn : 17 ≤ (33 : Fin 1121).val := by decide
    fin_cases i
    · exact (f3 _ (keepOut 0 3 (by decide) _ hn)).2.trans ((f2 _ (keepOut 0 2 (by decide) _ hn)).2.trans
        ((f1 _ (keepOut 0 1 (by decide) _ hn)).2.trans hc0))
    · exact (f3 _ (keepOut 1 3 (by decide) _ hn)).2.trans ((f2 _ (keepOut 1 2 (by decide) _ hn)).2.trans hc1)
    · exact (f3 _ (keepOut 2 3 (by decide) _ hn)).2.trans hc2
    · exact hc3
  · intro x hx
    have a3 := f3 x (hx 3)
    have a2 := f2 x (hx 2)
    have a1 := f1 x (hx 1)
    have a0 := f0 x (hx 0)
    exact ⟨a3.1.trans (a2.1.trans (a1.1.trans a0.1)), a3.2.trans (a2.2.trans (a1.2.trans a0.2))⟩

end
end
end NearCubicWires.SourceFactorSel.Slots4

