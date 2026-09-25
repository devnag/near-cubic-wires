import Proof.SourceAssembly.SourceRowConst
import Proof.SourceAssembly.SourceFinish

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
namespace NearCubicWires.SourceConstruction.FinishCycle
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- The template is the padded word, re-padded: `pad Rc (tape x) = pad (max Rc (x+2)) (word x)`. -/
theorem pad_tape_word (Rc x : ℕ) :
    ZeroPadding.pad Rc (UnaryTemplate.tape x) = ZeroPadding.pad (max Rc (x+2)) (CompareMachine.word x) := by
  rw [Uniform.tape_eq_pad, Uniform.pad_pad]

def machine (a : WilliamsAlgorithm) {U : ℕ} (cs : Fin 16 → Fin U) (fam : Fin (r_tapes a) → Fin U)
    (drv : Fin 7 → Fin U) :=
  Composition.machine (RecoveryFocus.machine cs RowWidth.machine)
    (RecoveryFocus.machine (Finish.joinSlots a fam drv) (PCJ34388a2fbfa9464b_.machine a))

/-- The calculator, padded by `capLen` on its `1^L` tape. -/
theorem calc_padded (L M2 U0 N Rc capLen : ℕ) (hL : L + 3 ≤ Rc) :
    ∃ W : Fin 16 → List Bool,
      Step RowWidth.machine (RowWidth.cost L M2 U0 N) RowWidth.inH
        (fun i => ZeroPadding.pad (if i.val = 0 then capLen else 0) (RowWidth.input L M2 U0 N Rc i))
        RowWidth.outH W ∧
      W 4 = ZeroPadding.pad Rc (UnaryTemplate.tape (RowWidth.rw M2 U0 L)) ∧
      W 5 = ZeroPadding.pad Rc (UnaryTemplate.tape (RowWidth.rw M2 U0 L * N)) ∧
      W 3 = ZeroPadding.pad Rc (CompareMachine.word N) := by
  obtain ⟨W, h, h4, h5, h3⟩ := RowWidth.calc_run L M2 U0 N Rc hL
  refine ⟨fun i => ZeroPadding.pad (if i.val = 0 then capLen else 0) (W i),
    h.pad (fun i => if i.val = 0 then capLen else 0), ?_, ?_, ?_⟩
  · simp [h4]
  · simp [h5]
  · simp [h3]

/-- The initializer's driver caps: templates re-padded, the counter at `Rc`. -/
def caps (Rc S Rw B rw v N : ℕ) : Fin 7 → ℕ :=
  ![max Rc (S+2), max Rc (Rw+2), max Rc (B+2), max Rc (rw+2), max Rc (v+2), Rc, max Rc (N*rw+2)]

theorem finish_cycle (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum)
    (L M2 U0 Rc capLen S Rw B v : ℕ) {U : ℕ}
    (cs : Fin 16 → Fin U) (hcs : Function.Injective cs)
    (fam : Fin (r_tapes a) → Fin U) (drv : Fin 7 → Fin U)
    (hjoin : Function.Injective (Finish.joinSlots a fam drv))
    (hd3 : drv 3 = cs 4) (hd5 : drv 5 = cs 3) (hd6 : drv 6 = cs 5)
    (hfam_cs : ∀ i k, fam i ≠ cs k)
    (hdu_cs : ∀ k : Fin 7, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4) → ∀ j, drv k ≠ cs j)
    (H : Fin U → ℕ) (A : Fin U → List Bool)
    (hA0 : A (cs 0) = ZeroPadding.pad capLen (List.replicate L true))
    (hA1 : A (cs 1) = ZeroPadding.pad Rc (List.replicate M2 true))
    (hA2 : A (cs 2) = ZeroPadding.pad Rc (List.replicate U0 true))
    (hA3 : A (cs 3) = ZeroPadding.pad Rc (CompareMachine.word ds.length))
    (hAk : ∀ k : Fin 16, 4 ≤ k.val → A (cs k) = ZeroPadding.pad Rc [])
    (hHc : ∀ k, H (cs k) = RowWidth.inH k)
    (hL : L + 3 ≤ Rc)
    (hU0 : A (drv 0) = ZeroPadding.pad Rc (UnaryTemplate.tape S))
    (hU1 : A (drv 1) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw))
    (hU2 : A (drv 2) = ZeroPadding.pad Rc (UnaryTemplate.tape B))
    (hU4 : A (drv 4) = ZeroPadding.pad Rc (UnaryTemplate.tape v))
    (hUH : ∀ k : Fin 7, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4) → H (drv k) = 1)
    (hHf : ∀ i, H (fam i) = 0)
    (hsrc : A (fam (sourcePort a)) =
      ZeroPadding.pad Rc (ds.flatMap (P1TopDownPaidReusable.Datum.word a)))
    (hblank : ∀ i, i ≠ sourcePort a → A (fam i) = List.replicate Rc false) :
    ∃ H' A', Step (machine a cs fam drv)
        (RowWidth.cost L M2 U0 ds.length + 1 + initFuel a ⟨S, Rw, B, RowWidth.rw M2 U0 L, v, ds.length⟩)
        H A H' A' ∧
      (∀ i, H' (fam i) = r_inputH a ds S Rw B ds.length i) ∧
      (∀ i, A' (fam i) = ZeroPadding.pad Rc (r_inputT a ds S Rw B (RowWidth.rw M2 U0 L) v ds.length i)) ∧
      (∀ x, (∀ k, cs k ≠ x) → (∀ i, fam i ≠ x) → (∀ k, drv k ≠ x) → H' x = H x ∧ A' x = A x) := by
  obtain ⟨W, hcalc, hW4, hW5, hW3⟩ := calc_padded L M2 U0 ds.length Rc capLen hL
  have s1 := hcalc.dock cs hcs H A hHc (by
    intro j
    by_cases h0 : j.val = 0
    · have e : j = 0 := Fin.ext h0
      subst e; simp [RowWidth.input, hA0]
    by_cases h1 : j.val = 1
    · have e : j = 1 := Fin.ext h1
      subst e; simp [RowWidth.input, hA1]
    by_cases h2 : j.val = 2
    · have e : j = 2 := Fin.ext h2
      subst e; simp [RowWidth.input, hA2]
    by_cases h3 : j.val = 3
    · have e : j = 3 := Fin.ext h3
      subst e; simp [RowWidth.input, hA3]
    rw [hAk j (by omega)]
    simp [RowWidth.input, h0, h1, h2, h3])
  set H1 := dockH cs H RowWidth.outH with hH1
  set A1 := install cs A W with hA1'
  have H1off : ∀ x, (∀ k, cs k ≠ x) → H1 x = H x := fun x hx => dockH_other cs H _ x hx
  have A1off : ∀ x, (∀ k, cs k ≠ x) → A1 x = A x := fun x hx => install_other cs A W x hx
  have A1cs : ∀ k, A1 (cs k) = W k := fun k => install_slot cs hcs A W k
  have famoff : ∀ i, ∀ k, cs k ≠ fam i := fun i k h => hfam_cs i k h.symm
  let rw := RowWidth.rw M2 U0 L
  let m : Scalars := ⟨S, Rw, B, rw, v, ds.length⟩
  have d0 : A1 (drv 0) = ZeroPadding.pad (caps Rc S Rw B rw v ds.length 0) (drivers m 0) := by
    rw [A1off _ (fun j h => hdu_cs 0 (Or.inl rfl) j h.symm), hU0, pad_tape_word]; rfl
  have d1 : A1 (drv 1) = ZeroPadding.pad (caps Rc S Rw B rw v ds.length 1) (drivers m 1) := by
    rw [A1off _ (fun j h => hdu_cs 1 (Or.inr (Or.inl rfl)) j h.symm), hU1, pad_tape_word]; rfl
  have d2 : A1 (drv 2) = ZeroPadding.pad (caps Rc S Rw B rw v ds.length 2) (drivers m 2) := by
    rw [A1off _ (fun j h => hdu_cs 2 (Or.inr (Or.inr (Or.inl rfl))) j h.symm), hU2, pad_tape_word]; rfl
  have d3 : A1 (drv 3) = ZeroPadding.pad (caps Rc S Rw B rw v ds.length 3) (drivers m 3) := by
    rw [hd3, A1cs 4, hW4, pad_tape_word]; rfl
  have d4 : A1 (drv 4) = ZeroPadding.pad (caps Rc S Rw B rw v ds.length 4) (drivers m 4) := by
    rw [A1off _ (fun j h => hdu_cs 4 (Or.inr (Or.inr (Or.inr rfl))) j h.symm), hU4, pad_tape_word]; rfl
  have d5 : A1 (drv 5) = ZeroPadding.pad (caps Rc S Rw B rw v ds.length 5) (drivers m 5) := by
    rw [hd5, A1cs 3, hW3]; rfl
  have d6 : A1 (drv 6) = ZeroPadding.pad (caps Rc S Rw B rw v ds.length 6) (drivers m 6) := by
    rw [hd6, A1cs 5, hW5, pad_tape_word, Nat.mul_comm]; rfl
  have hdrv : ∀ k, A1 (drv k) = ZeroPadding.pad (caps Rc S Rw B rw v ds.length k) (drivers m k) := by
    intro k
    fin_cases k
    · exact d0
    · exact d1
    · exact d2
    · exact d3
    · exact d4
    · exact d5
    · exact d6
  have e0 : H1 (drv 0) = 1 := by
    rw [H1off _ (fun j h => hdu_cs 0 (Or.inl rfl) j h.symm)]; exact hUH 0 (Or.inl rfl)
  have e1 : H1 (drv 1) = 1 := by
    rw [H1off _ (fun j h => hdu_cs 1 (Or.inr (Or.inl rfl)) j h.symm)]; exact hUH 1 (Or.inr (Or.inl rfl))
  have e2 : H1 (drv 2) = 1 := by
    rw [H1off _ (fun j h => hdu_cs 2 (Or.inr (Or.inr (Or.inl rfl))) j h.symm)]
    exact hUH 2 (Or.inr (Or.inr (Or.inl rfl)))
  have e4 : H1 (drv 4) = 1 := by
    rw [H1off _ (fun j h => hdu_cs 4 (Or.inr (Or.inr (Or.inr rfl))) j h.symm)]
    exact hUH 4 (Or.inr (Or.inr (Or.inr rfl)))
  have e3 : H1 (drv 3) = 1 := by rw [hd3, hH1, dockH_slot cs hcs]; rfl
  have e5 : H1 (drv 5) = 1 := by rw [hd5, hH1, dockH_slot cs hcs]; rfl
  have e6 : H1 (drv 6) = 1 := by rw [hd6, hH1, dockH_slot cs hcs]; rfl
  have hHd : ∀ k, H1 (drv k) = 1 := by
    intro k
    fin_cases k
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
  have s2 := Finish.finish_core a ds S Rw B rw v ds.length Rc (caps Rc S Rw B rw v ds.length) fam drv hjoin
    H1 A1 (fun i => (H1off _ (famoff i)).trans (hHf i)) hHd
    ((A1off _ (famoff _)).trans hsrc) (fun i hi => (A1off _ (famoff i)).trans (hblank i hi)) hdrv
  refine ⟨_, _, s1.seq s2, fun i => Finish.finish_family_heads a ds S Rw B ds.length fam drv hjoin H1 i,
    fun i => Finish.finish_family_tapes a ds S Rw B rw v ds.length Rc _ fam drv hjoin A1 i, ?_⟩
  intro x hcx hfx hdx
  have hjx : ∀ j, Finish.joinSlots a fam drv j ≠ x := by
    refine Finish.init_cases a _ (fun i => ?_) (fun k => ?_)
    · rw [Finish.join_family]; exact hfx i
    · rw [Finish.join_driver]; exact hdx k
  obtain ⟨h1, h2⟩ := Finish.finish_frame a ds S Rw B rw v ds.length Rc (caps Rc S Rw B rw v ds.length)
    fam drv H1 A1 x hjx
  exact ⟨h1.trans (H1off x hcx), h2.trans (A1off x hcx)⟩

end
end NearCubicWires.SourceConstruction.FinishCycle
end
