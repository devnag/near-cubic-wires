import Proof.SourceAssembly.SourceRequestCurComp
import Proof.SourceAssembly.SourceRequestCurSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurContract
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
noncomputable section

/-! ## Ports -/

def mT : Fin 128 := 0
def jlT : Fin 128 := 1
def jrT : Fin 128 := 2
def fLT : Fin 128 := 3
def fRT : Fin 128 := 4
def logT : Fin 128 := 5
def sysT (i : Fin 4) : Fin 128 := ⟨6 + 4 * i.val, by omega⟩
def termT (i : Fin 4) : Fin 128 := ⟨7 + 4 * i.val, by omega⟩
def rightT (i : Fin 4) : Fin 128 := ⟨8 + 4 * i.val, by omega⟩
def idxT (i : Fin 4) : Fin 128 := ⟨9 + 4 * i.val, by omega⟩
def kT : Fin 128 := 22
def rhoT : Fin 128 := 23

/-- The multiplier of monomial `m`'s symbolic record (`0` past the end). -/
def rhoOf (σ : Option Sel) : ℚ := (σ.map Sel.rho).getD 0

/-- The record width of the multiplier: `rho ∈ {1, -1, 1/2}` has `|num|, den < 2^2`. -/
def rhoW : Nat := 2

/-- **The cursor's outputs for the symbolic record `σ`**, every port padded to the scratch size `S`. -/
def CursorOut (σ : Option Sel) (S : Nat) (E : Fin 128 → List Bool) : Prop :=
  (∀ i : Fin 4, E (sysT i) = ZeroPadding.pad S [fSys (facAt σ i.val)]) ∧
  (∀ i : Fin 4, E (termT i) = ZeroPadding.pad S [fTerm (facAt σ i.val)]) ∧
  (∀ i : Fin 4, E (rightT i) = ZeroPadding.pad S [fSide (facAt σ i.val)]) ∧
  (∀ i : Fin 4, E (idxT i) = ZeroPadding.pad S (List.replicate (fIdx (facAt σ i.val)) true)) ∧
  E kT = ZeroPadding.pad S (List.replicate (kOf σ) true) ∧
  E rhoT = ZeroPadding.pad S (CloseoutRowsEstimatorCoefficients.Product.record rhoW (rhoOf σ))

/-- One size bound for every phase (`N ≤ curBig`, every block length and digit below it). -/
def curBig (JL JR : Nat) : Nat :=
  64 * ((JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2)))

/-- One cost bound for every phase (source polynomial in `JL + JR`). -/
def curCost (JL JR : Nat) : Nat := 64 * curBig JL JR

/-- **The cursor contract of phase `ph`** at ONE fixed local machine `M` (all heads `0` → `0`). -/
def CursorRun {s : Nat} (M : Machine 128 s) (ph : Phase) : Prop :=
  ∀ (sL sR nL nR : Bool) (m JL JR Qm Q1 Q2 Qf S C : Nat) (E : Fin 128 → List Bool),
    m ≤ MonomialSpec.siteLen ph sL sR nL nR JL JR →
    curBig JL JR ≤ S → curBig JL JR ≤ C →
    E mT = ZeroPadding.pad Qm (List.replicate m true) →
    E jlT = ZeroPadding.pad Q1 (List.replicate JL true) →
    E jrT = ZeroPadding.pad Q2 (List.replicate JR true) →
    E fLT = ZeroPadding.pad Qf [SourceFactorSel.Count.flagOf ph sL nL] →
    E fRT = ZeroPadding.pad Qf [SourceFactorSel.Count.flagOf ph sR nR] →
    E logT = List.replicate C false →
    (∀ j : Fin 128, 6 ≤ j.val → E j = List.replicate S false) →
    ∃ E' : Fin 128 → List Bool,
      Step M (curCost JL JR) (fun _ => 0) E (fun _ => 0) E' ∧
      CursorOut (selAt ph sL sR nL nR JL JR m) S E' ∧
      (∀ j : Fin 128, j.val < 6 → E' j = E j) ∧
      (∀ j : Fin 128, 24 ≤ j.val → (E' j).length ≤ S)

/-! ## Blank-port identities -/

theorem pad_ff (S : Nat) (h : 1 ≤ S) : ZeroPadding.pad S [false] = List.replicate S false := by
  unfold ZeroPadding.pad
  rw [show S = (S - 1) + 1 by omega, List.replicate_succ]
  simp

theorem pad_zero (S : Nat) : ZeroPadding.pad S (List.replicate 0 true) = List.replicate S false := by
  simp [ZeroPadding.pad]

theorem pad_len (S : Nat) (w : List Bool) (h : w.length ≤ S) : (ZeroPadding.pad S w).length = S := by
  rw [ZeroPadding.pad_length]; omega

theorem record_len (c : Nat) (q : ℚ) :
    (CloseoutRowsEstimatorCoefficients.Product.record c q).length = 4 * c + 5 :=
  CloseoutRowsEstimatorCoefficients.Product.record_length c q

theorem curBig_ge (JL JR : Nat) : 1024 ≤ curBig JL JR := by
  unfold curBig
  have h2 : 2 ≤ JL + JR + 2 := by omega
  have h4 : 4 ≤ (JL + JR + 2) * (JL + JR + 2) := Nat.mul_le_mul h2 h2
  have h16 : 16 ≤ (JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2)) := Nat.mul_le_mul h4 h4
  omega

/-- The quantity `M = JL + JR + 2` bounds each count, and `M^4`-terms sit inside `curBig`. -/
theorem sq_le_big (JL JR : Nat) : 64 * ((JL + JR + 2) * (JL + JR + 2)) ≤ curBig JL JR := by
  unfold curBig
  set X := (JL + JR + 2) * (JL + JR + 2) with hX
  have hM : 1 ≤ JL + JR + 2 := by omega
  have h2 : 1 ≤ X := by rw [hX]; exact Nat.mul_le_mul hM hM
  have h3 : X ≤ X * X := by nlinarith
  omega

/-! ## Proof helpers for cursor builders (scratch-length invariant, per-slot `∀`) -/

/-- Scratch lengths `≤ S` (the contract's last conjunct), as an invariant carried through a chain. -/
def Fits (S : Nat) (A : Fin 128 → List Bool) : Prop := ∀ j : Fin 128, 24 ≤ j.val → (A j).length ≤ S

theorem fits_init {S : Nat} {E : Fin 128 → List Bool} (h : ∀ j : Fin 128, 6 ≤ j.val → E j = List.replicate S false) :
    Fits S E := by
  intro j hj; rw [h j (by omega)]; simp

theorem fits_update {S : Nat} {A : Fin 128 → List Bool} (h : Fits S A) (d : Fin 128) (w : List Bool)
    (hw : w.length ≤ S) : Fits S (Function.update A d (ZeroPadding.pad S w)) := by
  intro j hj
  by_cases e : j = d
  · subst e; rw [Function.update_self, pad_len S w hw]
  · rw [Function.update_of_ne e]; exact h j hj

theorem fits_frame {S : Nat} {A A' : Fin 128 → List Bool} (h : Fits S A) (T : Fin 128 → Prop)
    (hk : ∀ z, ¬ T z → A' z = A z) (hl : ∀ z, T z → (A' z).length ≤ S) : Fits S A' := by
  intro j hj
  by_cases e : T j
  · exact hl j e
  · rw [hk j e]; exact h j hj

theorem forall4 {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ i, P i := by
  intro i; fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-! ## Docked form -/

/-- **A cursor run docked by any injective slot map**: outputs installed, heads unchanged. -/
theorem CursorRun.dock {s U : Nat} {M : Machine 128 s} {ph : Phase} (h : CursorRun M ph)
    (sl : Fin 128 → Fin U) (hsl : Function.Injective sl)
    (sL sR nL nR : Bool) (m JL JR Qm Q1 Q2 Qf S C : Nat) (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ i, H (sl i) = 0)
    (hm : m ≤ MonomialSpec.siteLen ph sL sR nL nR JL JR) (hS : curBig JL JR ≤ S) (hC : curBig JL JR ≤ C)
    (h0 : A (sl mT) = ZeroPadding.pad Qm (List.replicate m true))
    (h1 : A (sl jlT) = ZeroPadding.pad Q1 (List.replicate JL true))
    (h2 : A (sl jrT) = ZeroPadding.pad Q2 (List.replicate JR true))
    (h3 : A (sl fLT) = ZeroPadding.pad Qf [SourceFactorSel.Count.flagOf ph sL nL])
    (h4 : A (sl fRT) = ZeroPadding.pad Qf [SourceFactorSel.Count.flagOf ph sR nR])
    (h5 : A (sl logT) = List.replicate C false)
    (hscr : ∀ j : Fin 128, 6 ≤ j.val → A (sl j) = List.replicate S false) :
    ∃ E' : Fin 128 → List Bool,
      Step (RecoveryFocus.machine sl M) (curCost JL JR) H A H (install sl A E') ∧
      CursorOut (selAt ph sL sR nL nR JL JR m) S E' ∧
      (∀ j : Fin 128, j.val < 6 → E' j = A (sl j)) ∧
      (∀ j : Fin 128, 24 ≤ j.val → (E' j).length ≤ S) := by
  obtain ⟨E', st, hout, hkeep, hlen⟩ :=
    h sL sR nL nR m JL JR Qm Q1 Q2 Qf S C (fun i => A (sl i)) hm hS hC h0 h1 h2 h3 h4 h5 hscr
  exact ⟨E', TermSeg.dock st sl hsl H A hH (fun _ => rfl), hout, hkeep, hlen⟩

end
end NearCubicWires.SourceRequest.CurContract

