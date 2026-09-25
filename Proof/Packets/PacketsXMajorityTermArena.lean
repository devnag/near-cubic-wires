import Proof.Packets.PacketsXMajorityTermDefs
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning
attribute [local irreducible] commonReserve List.replicate

theorem scratch_fits (C w : Nat) (ps : List Poly) (left right : Poly) (bits : List Bool) (count : Nat)
    (flag : Bool) (out binary : List Bool) (hl : left.length≤2^w) (hr : right.length≤2^w)
    (hb : bits.length≤commonReserve C w) (hn : count+1≤commonReserve C w) :
    ∀i,(A C (commonReserve C w) ps left right bits count flag out binary (scratch i)).length≤commonReserve C w := by
  have hleft:=(SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C left)
    (by simpa only [List.length_map] using hl)).2
  have hright:=(SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C right)
    (by simpa only [List.length_map] using hr)).2
  have hR : 1≤commonReserve C w:=by omega
  intro i
  fin_cases i
  · exact (VectorAccumulator.flat_length _ _ hleft).le
  · exact (VectorAccumulator.flat_length _ _ hright).le
  · exact (VectorAccumulator.count_length _ _ hright).le
  · exact (VectorAccumulator.count_length _ _ hleft).le
  · simp [A,extras,scratch,Fin.addCases,ZeroPadding.pad_length,Nat.max_eq_left hb]
  · simp [A,extras,scratch,Fin.addCases,ZeroPadding.pad_length,CompareMachine.word,Nat.max_eq_left hn]
  · simp [A,extras,scratch,Fin.addCases,ZeroPadding.pad_length,Nat.max_eq_left hR]

private def eraseInput (C R : Nat) (ps : List Poly) (left right : Poly)
    (bits : List Bool) (count : Nat) (flag : Bool) (out binary : List Bool) : Fin 9→List Bool :=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
      (fun i=>A C R ps left right bits count flag out binary (scratch i))
      (fun _=>List.replicate R true)) (fun _=>List.replicate (R+3) false)
private def eraseOutput (R : Nat) : Fin 9→List Bool :=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
      (fun _=>List.replicate R false) (fun _=>List.replicate R true))
    (fun _=>List.replicate (R+3) false)

private theorem clear_heads (out : List Bool) : ∀i:Fin 9,0=H out (clearSlots i) := by
  intro i;fin_cases i <;>rfl

private theorem clear_inputs (C R : Nat) (ps : List Poly) (left right : Poly)
    (bits : List Bool) (count : Nat) (flag : Bool) (out binary : List Bool) :
    ∀i,eraseInput C R ps left right bits count flag out binary i=
      A C R ps left right bits count flag out binary (clearSlots i) := by
  intro i;fin_cases i <;>rfl

private theorem clear_outputs (C R : Nat) (ps : List Poly) (out binary : List Bool)
    (hR : 1≤R) : ∀i,eraseOutput R i=A C R ps [] [] [] 0 false out binary (clearSlots i) := by
  have hz:=OrderedPacketReset.zero_pad R hR
  intro i;fin_cases i
  · change List.replicate R false=ZeroPadding.pad R []
    simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
  · change List.replicate R false=ZeroPadding.pad R []
    simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
  · exact hz.symm
  · exact hz.symm
  · change List.replicate R false=ZeroPadding.pad R []
    simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
  · exact hz.symm
  · change List.replicate R false=ZeroPadding.pad R [false]
    simpa only [CompareMachine.word,List.replicate_zero] using hz.symm
  · rfl
  · rfl

private theorem clear_outside_generic {α : Type} (a b : Fin 34→α) (tail : Fin 3→α)
    (u v : Fin 9→α)
    (hab : ∀i,i≠25→i≠26→i≠27→i≠28→a i=b i)
    (huv : ∀i,i≠0→i≠3→i≠4→u i=v i) :
    ∀i,(∀j,clearSlots j≠i)→
      Fin.addCases (m:=37) (n:=9) (motive:=fun _=>α)
        (Fin.addCases (m:=34) (n:=3) (motive:=fun _=>α) a tail) u i=
      Fin.addCases (m:=37) (n:=9) (motive:=fun _=>α)
        (Fin.addCases (m:=34) (n:=3) (motive:=fun _=>α) b tail) v i := by
  intro i
  refine Fin.addCases (m:=37) (n:=9) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=34) (n:=3) (fun k=>?_) (fun k=>?_) j
    · intro away
      simp only [Fin.addCases_left]
      exact hab k
        (fun he=>by subst k;exact away 0 rfl)
        (fun he=>by subst k;exact away 1 rfl)
        (fun he=>by subst k;exact away 2 rfl)
        (fun he=>by subst k;exact away 3 rfl)
    · intro _
      simp only [Fin.addCases_left,Fin.addCases_right]
  · intro away
    simp only [Fin.addCases_right]
    exact huv j
      (fun he=>by subst j;exact away 4 rfl)
      (fun he=>by subst j;exact away 5 rfl)
      (fun he=>by subst j;exact away 6 rfl)

private theorem clear_core (C R : Nat) (left right : Poly) :
    ∀k:Fin 34,k≠25→k≠26→k≠27→k≠28→
      ReusableArithmetic.state C R (left.map (maskNat C)) (right.map (maskNat C)) k=
      ReusableArithmetic.state C R [] [] k := by
  intro k h25 h26 h27 h28
  have hl:=VectorAccumulator.tapes_left_outside C R
    (left.map (maskNat C)) (right.map (maskNat C)) [] [] (k.castAdd 2)
    (fun he=>h25 (Fin.castAdd_inj.mp he)) (fun he=>h28 (Fin.castAdd_inj.mp he))
  have hr:=VectorAccumulator.tapes_right_outside C R
    [] (right.map (maskNat C)) [] [] (k.castAdd 2)
    (fun he=>h26 (Fin.castAdd_inj.mp he)) (fun he=>h27 (Fin.castAdd_inj.mp he))
  simp only [VectorAccumulator.tapes_engine] at hl hr
  exact hl.trans hr

private theorem clear_extras (R N count : Nat) (bits out binary : List Bool) (flag : Bool) :
    ∀i:Fin 9,i≠0→i≠3→i≠4→
      extras R N count bits out binary flag i=extras R N 0 [] out binary false i := by
  intro i h0 h3 h4
  fin_cases i <;>first
    | exact False.elim (h0 rfl)
    | exact False.elim (h3 rfl)
    | exact False.elim (h4 rfl)
    | rfl

private theorem clear_outside (C R : Nat) (ps : List Poly) (left right : Poly)
    (bits : List Bool) (count : Nat) (flag : Bool) (out binary : List Bool) :
    ∀i,(∀j,clearSlots j≠i)→A C R ps left right bits count flag out binary i=
      A C R ps [] [] [] 0 false out binary i := by
  exact clear_outside_generic
    (ReusableArithmetic.state C R (left.map (maskNat C)) (right.map (maskNat C)))
    (ReusableArithmetic.state C R [] [])
    (![OrderedPacketStep.bank C R (ComplementPacketBank.pairs ps),
      ZeroPadding.pad R (CompareMachine.word 0),List.replicate R false] : Fin 3→List Bool)
    (extras R ps.length count bits out binary flag) (extras R ps.length 0 [] out binary false)
    (clear_core C R left right) (clear_extras R ps.length count bits out binary flag)

private theorem clear_boundary (C R : Nat) (ps : List Poly) (left right : Poly)
    (bits : List Bool) (count : Nat) (flag : Bool) (out binary : List Bool)
    (hR : 1≤R)
    (hscratch : ∀i,(A C R ps left right bits count flag out binary (scratch i)).length≤R) :
    Step clear (2*R+4) (H out) (A C R ps left right bits count flag out binary)
      (H out) (A C R ps [] [] [] 0 false out binary) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3)
    (fun i=>A C R ps left right bits count flag out binary (scratch i)) hscratch)
  rw [Nat.max_eq_left (by omega : R+1≤R+3)] at h
  change Step (RecoveryScratchErase.resetMachine 7) (2*R+4) (fun _=>0)
    (eraseInput C R ps left right bits count flag out binary) (fun _=>0) (eraseOutput R) at h
  exact PhysicalFocusBoundary.focus h clearSlots (by decide) (H out) (H out) _ _
    (clear_heads out) (clear_inputs C R ps left right bits count flag out binary)
    (clear_heads out) (clear_outputs C R ps out binary hR)
    (fun i away=>⟨rfl,clear_outside C R ps left right bits count flag out binary i away⟩)

theorem clear_run (C w : Nat) (ps : List Poly) (left right : Poly) (bits : List Bool) (count : Nat)
    (flag : Bool) (out binary : List Bool) (hl : left.length≤2^w) (hr : right.length≤2^w)
    (hb : bits.length≤commonReserve C w) (hn : count+1≤commonReserve C w) :
    Step clear (2*commonReserve C w+4) (H out) (A C (commonReserve C w) ps left right bits count flag out binary)
      (H out) (A C (commonReserve C w) ps [] [] [] 0 false out binary) := by
  exact clear_boundary C (commonReserve C w) ps left right bits count flag out binary
    (by omega) (scratch_fits C w ps left right bits count flag out binary hl hr hb hn)

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
