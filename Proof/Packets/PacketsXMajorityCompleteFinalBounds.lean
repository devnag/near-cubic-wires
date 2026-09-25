import Proof.Packets.PacketsXMajorityCompleteRun
import Proof.Packets.PacketsXMajorityCompletePalette

/-! A census of the actual final bank, independent of the much larger total
execution budget. Every private word fits the quadratic reset capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning
noncomputable section
attribute [local irreducible] commonReserve

private theorem quadratic_room (C w : Nat) : commonReserve C w+3 ≤ (commonReserve C w)^2 := by
  have room:=MajorityTermArena.count_room C w 0 (Nat.zero_le _)
  nlinarith

private theorem reserve_square (C w : Nat) : commonReserve C w ≤ (commonReserve C w)^2 := by
  have room:=quadratic_room C w
  omega

theorem palette_fits (C w N : Nat) (hN : N ≤ 2^w) (hCodes : 2^N ≤ 2^w) (hw : 1 ≤ w) :
    Palette.Fits C (commonReserve C w) N ((commonReserve C w)^2) := by
  have hcount:=MajorityTermArena.count_room C w N hN
  have hcodes:=OrderedPacketFold.driver_fit C w (2^N) hCodes
  have hsquare:=reserve_square C w
  have width : 2*C+5 ≤ commonReserve C w := by
    have hp : C+1 ≤ (C+1)^4:=Nat.le_self_pow (by decide) _
    have he : 1 ≤ 2^(8*w):=Nat.one_le_pow _ _ (by decide)
    have hmul:=Nat.mul_le_mul_left (65536*(C+1)^4) he
    unfold commonReserve
    nlinarith
  exact ⟨width.trans hsquare,quadratic_room C w,by omega,by omega⟩

private theorem engine_fits (C w : Nat) (left right : Poly)
    (hl : left.length ≤ 2^w) (hr : right.length ≤ 2^w) (hw : 1 ≤ w) :
    ∀i,(ReusableArithmetic.state C (commonReserve C w) (left.map (maskNat C)) (right.map (maskNat C)) i).length ≤
      (commonReserve C w)^2 := by
  have guarded:=(ReusableArithmetic.bounded_guards C w left right hl hr hw).1
  have square:=reserve_square C w
  have room:=quadratic_room C w
  intro i
  refine Fin.addCases (m:=30) (n:=4) (fun j=>?_) (fun j=>?_) i
  · simp only [ReusableArithmetic.state,ReusableArithmetic.bank,Fin.addCases_left]
    change (ZeroPadding.pad (commonReserve C w) (ReusableArithmetic.data C (left.map (maskNat C)) (right.map (maskNat C)) j)).length ≤ _
    rw [ZeroPadding.pad_length,Nat.max_eq_left (guarded j)]
    exact square
  · fin_cases j <;>simp [ReusableArithmetic.state,ReusableArithmetic.bank,Fin.addCases,UnaryTemplate.tape] <;>omega

private theorem ordered_fits (C w index : Nat) (left right : Poly) (ps : List Poly)
    (hl : left.length ≤ 2^w) (hr : right.length ≤ 2^w) (hi : index+1 ≤ commonReserve C w) (hw : 1 ≤ w) :
    ∀i,i≠34→(OrderedPacketStep.A C (commonReserve C w) index left right ps i).length ≤ (commonReserve C w)^2 := by
  intro i
  refine Fin.addCases (m:=34) (n:=3) (fun j=>?_) (fun j=>?_) i
  · intro _
    simpa only [OrderedPacketStep.A,ArithmeticLookup.A,Fin.addCases_left] using engine_fits C w left right hl hr hw j
  · intro away
    have square:=reserve_square C w
    fin_cases j
    · exact False.elim (away rfl)
    · change (ZeroPadding.pad (commonReserve C w) (CompareMachine.word index)).length ≤ _
      simp [ZeroPadding.pad_length,CompareMachine.word] at ⊢
      exact ⟨square,hi.trans square⟩
    · change (List.replicate (commonReserve C w) false).length ≤ _
      simpa only [List.length_replicate] using square

private theorem fold_fits (C w index N : Nat) (left right : Poly) (ps : List Poly)
    (hl : left.length ≤ 2^w) (hr : right.length ≤ 2^w) (hi : index+1 ≤ commonReserve C w)
    (hN : N+1 ≤ commonReserve C w) (hbank : (OrderedPacketStep.bank C (commonReserve C w) ps).length ≤ (commonReserve C w)^2)
    (hw : 1 ≤ w) : ∀i,(OrderedPacketFold.tapes C (commonReserve C w) index N left right ps i).length ≤ (commonReserve C w)^2 := by
  intro i
  refine Fin.addCases (m:=37) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [OrderedPacketFold.tapes,Fin.addCases_left]
    by_cases hj : j=34
    · subst j;exact hbank
    · exact ordered_fits C w index left right ps hl hr hi hw j hj
  · simp only [OrderedPacketFold.tapes,Fin.addCases_right]
    have square:=reserve_square C w
    simp [ZeroPadding.pad_length,CompareMachine.word]
    exact ⟨square,hN.trans square⟩

private theorem enum_fits (C w : Nat) (ps : List Poly) (code : Nat) (out : List Bool)
    (hpair : (paired C (commonReserve C w) ps).length ≤ (commonReserve C w)^2)
    (hN : ps.length ≤ 2^w) (hCodes : 2^ps.length ≤ 2^w)
    (hout : out.length ≤ (commonReserve C w)^2) (hw : 1 ≤ w) :
    ∀i,(enumerationA C (commonReserve C w) ps code out i).length ≤ (commonReserve C w)^2 := by
  have room:=MajorityTermArena.count_room C w ps.length hN
  have codes:=OrderedPacketFold.driver_fit C w (2^ps.length) hCodes
  have square:=reserve_square C w
  have positive : 1 ≤ commonReserve C w := by omega
  intro i
  refine Fin.addCases (m:=46) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [enumerationA,Fin.addCases_left]
    refine Fin.addCases (m:=37) (n:=9) (fun k=>?_) (fun k=>?_) j
    · simp only [MajorityTermArena.A,Fin.addCases_left]
      by_cases hk : k=34
      · subst k;exact hpair
      · exact ordered_fits C w 0 [] [] (ComplementPacketBank.pairs ps) (by simp) (by simp) positive hw k hk
    · simp only [MajorityTermArena.A,Fin.addCases_right]
      fin_cases k
      all_goals first
        | exact hout
        | (simp [enumerationA,MajorityTermArena.A,MajorityTermArena.extras,Fin.addCases,
            ZeroPadding.pad_length,CompareMachine.word,frame_length,SignedSortKey.binary_length];omega)
  · simp only [enumerationA,Fin.addCases_right]
    simp [CompareMachine.word]
    omega

private theorem comp_fits (C w : Nat) (ps : List Poly) (right : Poly)
    (hr : right.length ≤ 2^w) (hN : ps.length ≤ 2^w)
    (hpair : (paired C (commonReserve C w) ps).length ≤ (commonReserve C w)^2) (hw : 1 ≤ w) :
    ∀i,i≠34→(compA C (commonReserve C w) ps ps.length right (paired C (commonReserve C w) ps) i).length ≤
      (commonReserve C w)^2 := by
  have count:=OrderedPacketFold.driver_fit C w ps.length hN
  have square:=reserve_square C w
  intro i
  refine Fin.addCases (m:=38) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=37) (n:=1) (fun k=>?_) (fun k=>?_) j
    · intro away
      simp only [compA,ComplementPacketStep.A,Fin.addCases_left]
      exact ordered_fits C w ps.length [[]] right ps
        (by simpa using Nat.one_le_pow w 2 (by decide)) hr count hw k
        (fun he=>by subst k;exact away rfl)
    · intro _
      simpa only [compA,ComplementPacketStep.A,Fin.addCases_left,Fin.addCases_right] using hpair
  · intro _
    simp only [compA,Fin.addCases_right]
    simp [CompareMachine.word]
    omega

private theorem install_fits {t : Nat} (slots : Fin t→Fin 125) (A : Fin 125→List Bool)
    (B : Fin t→List Bool) (R : Nat)
    (ha : ∀i,i≠34→i≠124→(A i).length ≤ R)
    (hb : ∀i,(B i).length ≤ R) :
    ∀i,i≠34→i≠124→(install slots A B i).length ≤ R := by
  intro i h34 h124
  unfold install
  cases hp : RecoveryFocus.pick slots i with
  | none => exact ha i h34 h124
  | some j => exact hb j

private theorem produced_fits (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hAtom : (S.card+1)^d ≤ 2^w) (hN : ps.length ≤ 2^w) (hCodes : 2^ps.length ≤ 2^w) (hw : 1 ≤ w) :
    ∀i,i≠34→i≠124→(produced C (commonReserve C w) ps i).length ≤ (commonReserve C w)^2 := by
  have pairBound:=paired_capacity C w S d ps hps hAtom hN
  have priorBound:=ComplementPacketBank.prior_count C w d S ps [] hps hAtom (by simp) ps.length le_rfl
  have comp:=comp_fits C w ps _ priorBound hN pairBound hw
  have en:=enum_fits C w ps 0 [] pairBound hN hCodes (by simp) hw
  have enCold : ∀i,(enumCold C (commonReserve C w) ps i).length ≤ (commonReserve C w)^2 := by
    intro i
    by_cases hi : i=34
    · subst i;simp [enumCold]
    · simpa only [enumCold,Function.update_of_ne hi] using en i
  have codes:=OrderedPacketFold.driver_fit C w (2^ps.length) hCodes
  have foldBound:=fold_fits C w (2^ps.length) (2^ps.length) [] [] [] (by simp) (by simp)
    codes codes (by simp [OrderedPacketStep.bank,PacketVector.bank]) hw
  intro i
  refine Fin.addCases (m:=39) (n:=86) (fun j=>?_) (fun j=>?_) i
  · intro h34 _
    simpa only [produced,assemble,Fin.addCases_left] using comp j (fun he=>by subst j;exact h34 rfl)
  · refine Fin.addCases (m:=47) (n:=39) (fun k=>?_) (fun k=>?_) j
    · intro _ _
      simpa only [produced,assemble,Fin.addCases_left,Fin.addCases_right] using enCold k
    · refine Fin.addCases (m:=38) (n:=1) (fun l=>?_) (fun l=>?_) k
      · intro _ _
        simpa only [produced,assemble,foldCold,Fin.addCases_left,Fin.addCases_right] using foldBound l
      · intro _ h124
        fin_cases l
        exact False.elim (h124 rfl)

theorem final_fits (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length) ≤ 2^w) (hAtom : (S.card+1)^d ≤ 2^w)
    (hN : ps.length ≤ 2^w) (hCodes : 2^ps.length ≤ 2^w) (hw : 1 ≤ w) :
    ∀i : Fin 125,i≠34→i≠124→(final C (commonReserve C w) ps i).length ≤ (commonReserve C w)^2 := by
  have pairBound:=paired_capacity C w S d ps hps hAtom hN
  have termBound:=terms_capacity C w S d ps hps hfit hCodes
  have en:=enum_fits C w ps (2^ps.length-1) (termBank C (commonReserve C w) ps)
    pairBound hN hCodes termBound hw
  have enumeratedBound:=install_fits enumSlots _ _ _ (produced_fits C w S d ps hps hAtom hN hCodes hw) en
  have termCount : ∀P∈terms ps,P.length ≤ 2^w := by
    intro P hp
    exact (NormalizedIntermediate.census (terms_bounded S d ps hps P hp)).trans hfit
  have lastCount:=OrderedPacketFold.last_count (terms ps) [] (2^w) (2^ps.length) (by simp) termCount
  have majorityCount:=(NormalizedIntermediate.census (majority_bounded S d ps hps)).trans hfit
  have count:=OrderedPacketFold.driver_fit C w (2^ps.length) hCodes
  have foldBound:=fold_fits C w 0 (2^ps.length) _ _ (terms ps) lastCount majorityCount
    ((Nat.succ_le_succ (Nat.zero_le _)).trans count) count termBound hw
  exact install_fits foldSlots _ _ _ enumeratedBound foldBound

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
