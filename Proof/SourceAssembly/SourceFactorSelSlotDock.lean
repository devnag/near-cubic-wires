import Proof.SourceAssembly.SourceFactorSelSlot

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.SlotDock
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceFactorSel.Slot NearCubicWires.SourceRequest.TermReader
noncomputable section

/-- Dock a zero-entry-head local run of any exit heads: host heads outside the dock stay, dock heads become the local
exit heads. -/
theorem dockAny {s U : Nat} {p : Machine 1121 s} {n : Nat} {E E' : Fin 1121 → List Bool} {H0 : Fin 1121 → Nat}
    (h : Step p n (fun _ => 0) E H0 E') (sl : Fin 1121 → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0) (hA : ∀ j, A (sl j) = E j) :
    Step (RecoveryFocus.machine sl p) n H A (dockH sl H H0) (install sl A E') :=
  h.dock sl hsl H A (fun j => hH j) hA

theorem dock_frame {U : Nat} (sl : Fin 1121 → Fin U) (hsl : Function.Injective sl) (H : Fin U → Nat)
    (A : Fin U → List Bool) (E' : Fin 1121 → List Bool) (H0 : Fin 1121 → Nat)
    (hk : ∀ x : Fin 1121, x.val < 17 → E' x = A (sl x) ∧ H0 x = H (sl x)) :
    ∀ x, (∀ j, sl j = x → j.val < 17) → install sl A E' x = A x ∧ dockH sl H H0 x = H x := by
  intro x hx
  by_cases hp : ∃ j, sl j = x
  · obtain ⟨j, rfl⟩ := hp
    rw [install_slot sl hsl, dockH_slot sl hsl]
    exact hk j (hx j rfl)
  · refine ⟨install_other sl A E' x (fun j e => hp ⟨j, e⟩), dockH_other sl H H0 x (fun j e => hp ⟨j, e⟩)⟩

section
open RepairRepresentation SupplierPipeline SourceInterfaces SupplierEstimator NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceRequest
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)

/-- **THR mode, one factor slot, docked.** -/
theorem thr_slot_step {U : Nat} (sl : Fin 1121 → Fin U) (hsl : Function.Injective sl) (P W L : Nat)
    (o : Option (C10TotalDecode.Atom pcpp)) (bmL bmR wbits : List Bool) (s t r : Bool)
    (idx iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat) (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qf [s]) (h1 : A (sl 1) = ZeroPadding.pad Qf [t])
    (h2 : A (sl 2) = ZeroPadding.pad Qf [r]) (hQf : 1 ≤ Qf)
    (hin : Ins (fun j => A (sl j)) (UnaryTemplate.tape q) (List.replicate P true) (List.replicate W true)
      (List.replicate L true) bmL bmR wbits idx iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hq : q + 2 ≤ D) (hP : P ≤ D) (hW : W ≤ D) (hL : L ≤ D) (hDR : D ≤ R) (hDC : D + 1 ≤ C)
    (hk : kindOf false o = if s then .sys else if t then .orig else .absent) (hst : ¬ (s = true ∧ t = true))
    (hbm : s = true → bmOf o = (if r then bmR else bmL) ∧ (bmOf o).length ≤ D)
    (hterm : t = true → TermOK wbits (bitsOf false L o) (if r then iR else iL) idx cwid cw D R C) :
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step (RecoveryFocus.machine sl slotM) (slotCost wbits (if r then iR else iL) idx cwid cw D) H A H' A' ∧
      (∀ n : Fin 16, A' (sl (outP n)) = ZeroPadding.pad R (ThrSwitch.descAt P W L o n.val) ∧ H' (sl (outP n)) = 0) ∧
      (t = true → ∀ ts, rawTerms wbits (if r then iR else iL) = some ts → ∀ hi : idx < ts.length,
        A' (sl 33) = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx].1)) ∧
      H' (sl 33) = 0 ∧
      (∀ x, (∀ j, sl j = x → j.val < 17) → A' x = A x ∧ H' x = H x) := by
  obtain ⟨H0, E', st, hE, h33, hH33, hfr⟩ := thr_slot_run P W L o bmL bmR wbits s t r idx iL iR cwid cw D Qf Qi Qb Qt
    Qp Qw Ql Qd Rw R C (fun j => A (sl j)) h0 h1 h2 hQf hin hq hP hW hL hDR hDC hk hst hbm hterm
  refine ⟨dockH sl H H0, install sl A E', dockAny st sl hsl H A hH (fun _ => rfl), fun n => ?_, fun ht ts hr hi => ?_,
    ?_, dock_frame sl hsl H A E' H0 (fun x hx => ⟨(hfr x hx).1, by rw [(hfr x hx).2, hH]⟩)⟩
  · rw [install_slot sl hsl, dockH_slot sl hsl]; exact hE n
  · rw [install_slot sl hsl]; exact h33 ht ts hr hi
  · rw [dockH_slot sl hsl]; exact hH33

/-- **SYM mode, one factor slot, docked.** -/
theorem sym_slot_step {U : Nat} (sl : Fin 1121 → Fin U) (hsl : Function.Injective sl) (P W L : Nat)
    (o : Option (C10TotalDecode.Atom pcpp)) (bmL bmR wbits : List Bool) (s t r : Bool)
    (idx iL iR cwid cw D Qf Qi Qb Qt Qp Qw Ql Qd Rw R C : Nat) (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qf [s]) (h1 : A (sl 1) = ZeroPadding.pad Qf [t])
    (h2 : A (sl 2) = ZeroPadding.pad Qf [r]) (hQf : 1 ≤ Qf)
    (hin : Ins (fun j => A (sl j)) (UnaryTemplate.tape q) (List.replicate P true) (List.replicate W true)
      (List.replicate L true) bmL bmR wbits idx iL iR cwid cw D Qi Qb Qt Qp Qw Ql Qd Rw R C)
    (hq : q + 2 ≤ D) (hP : P ≤ D) (hW : W ≤ D) (hL : L ≤ D) (hDR : D ≤ R) (hDC : D + 1 ≤ C)
    (hk : kindOf true o = if s then .sys else if t then .orig else .absent) (hst : ¬ (s = true ∧ t = true))
    (hbm : s = true → bmOf o = (if r then bmR else bmL) ∧ (bmOf o).length ≤ D)
    (hterm : t = true → TermOK wbits (bitsOf true L o) (if r then iR else iL) idx cwid cw D R C) :
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step (RecoveryFocus.machine sl slotM) (slotCost wbits (if r then iR else iL) idx cwid cw D) H A H' A' ∧
      (∀ n : Fin 16, A' (sl (outP n)) = ZeroPadding.pad R (SymSwitch.descAt P W L o n.val) ∧ H' (sl (outP n)) = 0) ∧
      (t = true → ∀ ts, rawTerms wbits (if r then iR else iL) = some ts → ∀ hi : idx < ts.length,
        A' (sl 33) = ZeroPadding.pad R (CloseoutRowsEstimatorCoefficients.Product.record cw ts[idx].1)) ∧
      H' (sl 33) = 0 ∧
      (∀ x, (∀ j, sl j = x → j.val < 17) → A' x = A x ∧ H' x = H x) := by
  obtain ⟨H0, E', st, hE, h33, hH33, hfr⟩ := sym_slot_run P W L o bmL bmR wbits s t r idx iL iR cwid cw D Qf Qi Qb Qt
    Qp Qw Ql Qd Rw R C (fun j => A (sl j)) h0 h1 h2 hQf hin hq hP hW hL hDR hDC hk hst hbm hterm
  refine ⟨dockH sl H H0, install sl A E', dockAny st sl hsl H A hH (fun _ => rfl), fun n => ?_, fun ht ts hr hi => ?_,
    ?_, dock_frame sl hsl H A E' H0 (fun x hx => ⟨(hfr x hx).1, by rw [(hfr x hx).2, hH]⟩)⟩
  · rw [install_slot sl hsl, dockH_slot sl hsl]; exact hE n
  · rw [install_slot sl hsl]; exact h33 ht ts hr hi
  · rw [dockH_slot sl hsl]; exact hH33

end
end
end NearCubicWires.SourceFactorSel.SlotDock

