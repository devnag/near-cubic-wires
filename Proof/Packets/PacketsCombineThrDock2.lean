import Proof.Packets.PacketsCombineThrDock

/-! # P2 (iii) assembly, part 3: the THR engine docked, the store, and the whole local run

Consumer: `ThrCombineStageK` (`PacketsCombineThrStage`). Continues `PacketsCombineThrDock`: stage 4 docks
the exact THR engine `thrLoop_run` (entry read off at every engine slot from `TFacts3`), stages 5–6 move the
parked count head and dock the masked store, and `thrLocal_run` composes all six stages into ONE fixed local
machine `thrLocalM M`. Bookkeeping over donors; budget class: source-polynomial.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NearCubicWires.PacketsConstruction
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

section Stage4
variable (e Rb C w K N : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords table : List Bool)

def TFacts4 (Pf : Poly) (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool) : Prop :=
  (∀ i : Fin (118 + e), i.val ≤ 9 → A i = tlentry e Rb input keys coords i ∧ H i = 0) ∧
  (∀ i : Fin (118 + e), 116 ≤ i.val → i.val < 118 → A i = ZeroPadding.pad Rb [] ∧ H i = 0) ∧
  A ⟨10, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨10, by omega⟩ = 0 ∧
  A ⟨15, by omega⟩ = ZeroPadding.pad Rb (CompareMachine.word K) ∧ H ⟨15, by omega⟩ = 1 ∧
  A ⟨97, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape (commonReserve C w)) ∧ H ⟨97, by omega⟩ = 1 ∧
  A ⟨114, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (Pf.map (maskNat C)).flatten) ∧
    H ⟨114, by omega⟩ = 0 ∧
  A ⟨115, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (CompareMachine.word Pf.length)) ∧
    H ⟨115, by omega⟩ = 0

theorem tstage4_hin (ps : List Poly) (hcoords : coords = OrderedPacketStep.bank C (commonReserve C w) ps)
    (hR1 : 1 ≤ commonReserve C w) (hRb : commonReserve C w ≤ Rb) (hK2 : K + 2 ≤ Rb) (hN2 : N + 2 ≤ Rb)
    (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool)
    (f : TFacts3 e Rb C w K N input keys coords table H A) (j : Fin 43) :
    H (tengSlot e j) = tengH (N * (K + 1)) j ∧
      A (tengSlot e j) = ZeroPadding.pad Rb (tengA C (commonReserve C w) 0 K [] [] ps table []
        (ZeroPadding.pad (commonReserve C w) (CompareMachine.word K)) N j) := by
  obtain ⟨fb, ffree, fa113, fh113, _, _, fa14, fh14, fa15, fh15, fa16, fh16, fa17, fh17, far⟩ := f
  by_cases hj : j.val < 34
  · have fj := far ⟨j.val, hj⟩
    have ej : (⟨(⟨j.val, hj⟩ : Fin 34).val, by omega⟩ : Fin 43) = j := Fin.ext rfl
    rw [ej] at fj
    rw [tengA_arena _ _ _ _ _ _ _ _ _ _ _ j hj, tengH_arena _ j hj]
    exact ⟨fj.2, fj.1⟩
  · obtain ⟨k, hk⟩ := j
    simp only at hj
    interval_cases k
    · refine ⟨(fb ⟨9, by omega⟩ (by simp)).2, ?_⟩
      show A ⟨9, by omega⟩ = _
      rw [(fb ⟨9, by omega⟩ (by simp)).1, tlentry_nine, hcoords]
      rfl
    · refine ⟨fh113, ?_⟩
      show A ⟨113, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (CompareMachine.word 0))
      rw [fa113, word_zero_pad Rb _ hR1 hRb]
    · refine ⟨(ffree ⟨112, by omega⟩ (by simp) (by simp) (by simp)).2, ?_⟩
      show A ⟨112, by omega⟩ = ZeroPadding.pad Rb (List.replicate (commonReserve C w) false)
      rw [(ffree ⟨112, by omega⟩ (by simp) (by simp) (by simp)).1, Dock.pad_zeros Rb _ hRb]
    · exact ⟨fh17, fa17⟩
    · refine ⟨fh15, ?_⟩
      show A ⟨15, by omega⟩ = ZeroPadding.pad Rb (CompareMachine.word K)
      rw [fa15, tmpl_pad Rb K hK2]
    · refine ⟨(ffree ⟨114, by omega⟩ (by simp) (by simp) (by simp)).2, ?_⟩
      show A ⟨114, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w)
        (([] : Poly).map (maskNat C)).flatten)
      rw [(ffree ⟨114, by omega⟩ (by simp) (by simp) (by simp)).1, List.map_nil, List.flatten_nil,
        Dock.pad_monotone _ Rb _ hRb]
    · refine ⟨(ffree ⟨115, by omega⟩ (by simp) (by simp) (by simp)).2, ?_⟩
      show A ⟨115, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w)
        (CompareMachine.word ([] : Poly).length))
      rw [(ffree ⟨115, by omega⟩ (by simp) (by simp) (by simp)).1, List.length_nil, word_zero_pad Rb _ hR1 hRb]
    · refine ⟨fh14, ?_⟩
      show A ⟨14, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (CompareMachine.word K))
      rw [fa14, Dock.pad_monotone _ Rb _ hRb, tmpl_pad Rb K hK2]
    · refine ⟨fh16, ?_⟩
      show A ⟨16, by omega⟩ = ZeroPadding.pad Rb (CompareMachine.word N)
      rw [fa16, tmpl_pad Rb N hN2]

theorem tstage4 (S : Finset ℕ) (d : ℕ) (ps : List Poly)
    (hcoords : coords = OrderedPacketStep.bank C (commonReserve C w) ps)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ Q ∈ ps, NormalizedIntermediate.Bounded S d Q)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w)
    (hK : K ≤ ps.length) (hN : ps.length ≤ 2 ^ w)
    (hsweep : ∀ c, c < N → ∀ n, n ≤ K →
      Fits C (sweepAcc ps table (c * (K + 1)) K (initAcc table (c * (K + 1)) K) n) ∧
      (sweepAcc ps table (c * (K + 1)) K (initAcc table (c * (K + 1)) K) n).length ≤ 2 ^ w)
    (eD : ℕ) (hfitD : (S.card + 1) ^ eD ≤ 2 ^ w)
    (hterm : ∀ c, c < N → NormalizedIntermediate.Bounded S eD (codeTerm ps table K c)) (hw : 1 ≤ w)
    (hR1 : 1 ≤ commonReserve C w) (hRb : commonReserve C w ≤ Rb) (hK2 : K + 2 ≤ Rb) (hN2 : N + 2 ≤ Rb)
    (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool)
    (f : TFacts3 e Rb C w K N input keys coords table H A) :
    ∃ (H' : Fin (118 + e) → ℕ) (A' : Fin (118 + e) → List Bool),
      Step (RecoveryFocus.machine (tengSlot e) thrLoop) (N * (thrBodyBudget C w K + 3) + 3) H A H' A' ∧
      (∀ j, H' (tengSlot e j) = tengH 0 j ∧ A' (tengSlot e j) = ZeroPadding.pad Rb
        (tengA C (commonReserve C w) 0 K (thrLeftAt ps table N K [] N) [] ps table
          ((List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).foldr Ring.add [])
          (ZeroPadding.pad (commonReserve C w) (CompareMachine.word K)) N j)) ∧
      (∀ i, (∀ j, tengSlot e j ≠ i) → H' i = H i ∧ A' i = A i) :=
  Dock.lift (thrLoop_run C w S d eD ps table N K [] hS hps hfit hfitD hK hN (by simp) hsweep hterm hw)
    (tengSlot e) (tengSlot_injective e) (fun _ => Rb) H A
    (tstage4_hin e Rb C w K N input keys coords table ps hcoords hR1 hRb hK2 hN2 H A f)

theorem tengSlot_avoid (e : ℕ) (i : Fin (118 + e)) (hi : i.val ≤ 8 ∨ i.val = 10 ∨ 116 ≤ i.val) :
    ∀ j, tengSlot e j ≠ i := by
  intro j hj
  have hv := congrArg Fin.val hj
  simp only [tengSlot, tengSlotVal] at hv
  split_ifs at hv <;> omega

theorem tstage4_facts (ps : List Poly) (hcoords : coords = OrderedPacketStep.bank C (commonReserve C w) ps)
    (Pf : Poly) (leftF : Poly)
    (H A : _) (f : TFacts3 e Rb C w K N input keys coords table H A)
    (H' : Fin (118 + e) → ℕ) (A' : Fin (118 + e) → List Bool)
    (o : ∀ j, H' (tengSlot e j) = tengH 0 j ∧ A' (tengSlot e j) = ZeroPadding.pad Rb
        (tengA C (commonReserve C w) 0 K leftF [] ps table Pf
          (ZeroPadding.pad (commonReserve C w) (CompareMachine.word K)) N j))
    (kp : ∀ i, (∀ j, tengSlot e j ≠ i) → H' i = H i ∧ A' i = A i) :
    TFacts4 e Rb C w K input keys coords Pf H' A' := by
  obtain ⟨fb, ffree, _, _, fa10, fh10, _⟩ := f
  have keep : ∀ i : Fin (118 + e), (i.val ≤ 8 ∨ i.val = 10 ∨ 116 ≤ i.val) → A' i = A i ∧ H' i = H i := by
    intro i hi
    have := kp i (tengSlot_avoid e i hi)
    exact ⟨this.2, this.1⟩
  refine ⟨?_, ?_, (keep _ (by simp)).1.trans fa10, (keep _ (by simp)).2.trans fh10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h9 : i.val = 9
    · have ei : i = tengSlot e ⟨34, by omega⟩ := Fin.ext h9
      rw [ei, (o _).1, (o _).2]
      refine ⟨?_, rfl⟩
      have e9 : tengSlot e ⟨34, by omega⟩ = ⟨9, by omega⟩ := Fin.ext rfl
      rw [e9, tlentry_nine, hcoords]
      rfl
    · rw [(keep i (by omega)).1, (keep i (by omega)).2]
      exact fb i hi
  · intro i hi hi'
    rw [(keep i (by omega)).1, (keep i (by omega)).2]
    exact ffree i (by omega) hi' (by omega)
  · exact (o ⟨38, by omega⟩).2
  · exact (o ⟨38, by omega⟩).1
  · have h := (o ⟨31, by omega⟩).2
    have e31 : tengSlot e ⟨31, by omega⟩ = ⟨97, by omega⟩ := Fin.ext rfl
    rw [e31, tengA_arena _ _ _ _ _ _ _ _ _ _ _ _ (by simp)] at h
    exact h
  · have h := (o ⟨31, by omega⟩).1
    have e31 : tengSlot e ⟨31, by omega⟩ = ⟨97, by omega⟩ := Fin.ext rfl
    rw [e31, tengH_arena _ _ (by simp)] at h
    exact h
  · exact (o ⟨39, by omega⟩).2
  · exact (o ⟨39, by omega⟩).1
  · exact (o ⟨40, by omega⟩).2
  · exact (o ⟨40, by omega⟩).1

end Stage4

section Stage6
variable (e Rb C w K : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords : List Bool)

theorem tstoSlot_avoid (e : ℕ) (i : Fin (118 + e)) (hi : i.val ≤ 9) : ∀ j, tstoSlot e j ≠ i := by
  intro j hj
  have hv := congrArg Fin.val hj
  simp only [tstoSlot, tstoSlotVal] at hv
  split_ifs at hv <;> omega

theorem tstage56 (Pf : Poly) (hPf : Pf.length ≤ 2 ^ w) (hRb : PacketBank.storeBudget (commonReserve C w) ≤ Rb)
    (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool)
    (f : TFacts4 e Rb C w K input keys coords Pf H A) :
    ∃ (H' : Fin (118 + e) → ℕ) (A' : Fin (118 + e) → List Bool),
      Step (Composition.machine (PhysicalIndexReload.move (t := 118 + e) ⟨115, by omega⟩ .right)
        (RecoveryFocus.machine (tstoSlot e) symStore)) (1 + 1 + (2 * PacketBank.storeBudget (commonReserve C w) + 2))
        H A H' A' ∧
      (∀ i : Fin (118 + e), i.val ≤ 9 → A' i = tlentry e Rb input keys coords i ∧ H' i = 0) ∧
      A' ⟨10, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (Pf.map (maskNat C)).flatten ++
        ZeroPadding.pad (commonReserve C w) (CompareMachine.word Pf.length)) ∧
      H' ⟨10, by omega⟩ = 0 := by
  obtain ⟨fb, ffree, fa10, fh10, fa15, fh15, fa97, fh97, fa114, fh114, fa115, fh115⟩ := f
  set R := commonReserve C w with hRdef
  have s5 := PhysicalIndexReload.move_run (⟨115, by omega⟩ : Fin (118 + e)) .right H A
  set H5 := Function.update H ⟨115, by omega⟩ (HeadMove.right.apply (H ⟨115, by omega⟩)) with hH5
  have h5 : ∀ i : Fin (118 + e), i.val ≠ 115 → H5 i = H i := by
    intro i hi
    rw [hH5, Function.update_of_ne (fun h => hi (by rw [h]))]
  have h5' : H5 ⟨115, by omega⟩ = 1 := by
    rw [hH5, Function.update_self, fh115]; rfl
  have lens := reg_lengths C w Pf hPf
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift (symStore_run R K _ _ lens.1 lens.2) (tstoSlot e) (tstoSlot_injective e)
    (fun _ => Rb) H5 A (by
      intro j
      obtain ⟨k, hk⟩ := j
      interval_cases k
      · show H5 ⟨97, by omega⟩ = _ ∧ A ⟨97, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans fh97, ?_⟩
        rw [fa97]; rfl
      · show H5 ⟨10, by omega⟩ = _ ∧ A ⟨10, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans fh10, ?_⟩
        rw [fa10]; rfl
      · show H5 ⟨114, by omega⟩ = _ ∧ A ⟨114, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans fh114, ?_⟩
        rw [fa114]; rfl
      · show H5 ⟨115, by omega⟩ = _ ∧ A ⟨115, by omega⟩ = _
        refine ⟨h5', ?_⟩
        rw [fa115]; rfl
      · show H5 ⟨15, by omega⟩ = _ ∧ A ⟨15, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans fh15, ?_⟩
        rw [fa15]; rfl
      · show H5 ⟨116, by omega⟩ = _ ∧ A ⟨116, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans (ffree ⟨116, by omega⟩ (by simp) (by simp)).2, ?_⟩
        rw [(ffree ⟨116, by omega⟩ (by simp) (by simp)).1]; rfl
      · show H5 ⟨117, by omega⟩ = _ ∧ A ⟨117, by omega⟩ = ZeroPadding.pad Rb (List.replicate (PacketBank.storeBudget R) false)
        refine ⟨(h5 _ (by simp)).trans (ffree ⟨117, by omega⟩ (by simp) (by simp)).2, ?_⟩
        rw [(ffree ⟨117, by omega⟩ (by simp) (by simp)).1, Dock.pad_zeros Rb _ hRb])
  refine ⟨H', A', s5.seq st, ?_, ?_, ?_⟩
  · intro i hi
    have := kp i (tstoSlot_avoid e i hi)
    rw [this.1, this.2, h5 i (by omega)]
    exact fb i hi
  · have h := (o ⟨1, by omega⟩).2
    have e1 : tstoSlot e ⟨1, by omega⟩ = ⟨10, by omega⟩ := Fin.ext rfl
    rw [e1] at h
    rw [h]
    rfl
  · have h := (o ⟨1, by omega⟩).1
    have e1 : tstoSlot e ⟨1, by omega⟩ = ⟨10, by omega⟩ := Fin.ext rfl
    rw [e1] at h
    rw [h]
    rfl

end Stage6

end
end NearCubicWires.PacketsCombine
