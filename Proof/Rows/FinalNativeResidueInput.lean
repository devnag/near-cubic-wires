import Proof.CaseAnalysis.FinalSelectorLoadMasks
import Proof.Rows.FinalPrimeCoefficientReduce

/-! The literal native signed field and the paid MSB-first reducer input.
Reversal produces framed padded digits; the separate unframing pass physically
produces the raw digit tape. Every blank and padded reset log is explicit.
-/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueInput
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The original native reader supplies the actual sign and framed magnitude. -/
theorem field_step (pre tail : List Bool) (z : ℤ) :
    Step DecompositionNativeMagnitude.first (6*natBitLength z.natAbs+9)
      (DecompositionNativeMagnitude.input (pre++intWord z++tail) pre.length).heads
      (DecompositionNativeMagnitude.input (pre++intWord z++tail) pre.length).tapes
      (DecompositionNativeMagnitude.fieldOutput (pre++intWord z++tail)
        (pre.length+(intWord z).length) (SignedSortKey.binary (natBitLength z.natAbs) z.natAbs)
        (decide (z<0))).heads
      (DecompositionNativeMagnitude.fieldOutput (pre++intWord z++tail)
        (pre.length+(intWord z).length) (SignedSortKey.binary (natBitLength z.natAbs) z.natAbs)
        (decide (z<0))).tapes := by
  obtain ⟨r,hr,hf,_⟩ := DecompositionNativeMagnitude.field_run pre tail z
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem prepared_horner (bits : List Bool) :
FinalPrimeRow.horner (RecoveryRadixInput.prepared bits) (2*bits.length) = RadixSemantics.value bits := by
  rw [← RecoveryRadixInput.prepared_length bits, FinalPrimeRow.horner_take _ _ le_rfl,
    List.take_length]
  simp [RecoveryRadixInput.prepared, List.reverse_append, RadixSemantics.value_append]

theorem prepare_unwrap (bits : List Bool) (D : ℕ) (hD : 4*bits.length+2≤D) :
Step (Composition.machine (TapeEmbedding.machine 2
   (MaskedReset.machine RecoveryRadixInput.machine (fun _ => true)))
   (RecoveryFocus.machine (![1,4,5] : Fin 3 → Fin 6) Streaming.machine))
  (16*bits.length+9) (fun _ => 0)
  (![ frame bits, [], [], List.replicate D false, [], []] : Fin 6 → List Bool)
  (fun _ => 0)
  (![ frame bits, frame (RecoveryRadixInput.prepared bits), List.replicate (2*bits.length) false,
   List.replicate D false, RecoveryRadixInput.prepared bits,List.replicate (2*bits.length) false] : Fin 6 → List Bool) := by
  obtain ⟨r,hr,hf,_,_⟩ := RecoveryRadixInput.prepare_run bits
  have raw := Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have reset := raw.mask (cap:=D) (fun _ => true) (by intro i hi; rfl) hD
  have first := reset.embed (fun _ : Fin 2 => 0) (fun _ : Fin 2 => [])
  have A : Step (TapeEmbedding.machine 2 (MaskedReset.machine RecoveryRadixInput.machine (fun _ => true)))
      (8*bits.length+6) (fun _=>0)
      (![frame bits,[],[],List.replicate D false,[],[]] : Fin 6 → List Bool)
      (fun _=>0)
      (![frame bits,frame (RecoveryRadixInput.prepared bits),List.replicate (2*bits.length) false,
        List.replicate D false,[],[]] : Fin 6 → List Bool) := by
    have ht : 2*(4*bits.length+2)+2=8*bits.length+6 := by omega
    rw [ht] at first
    refine (first.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i; fin_cases i <;> rfl
  have second := (CloseoutFinalSelector.step_of_clock (UInputFields.unwrap_ready (RecoveryRadixInput.prepared bits))).dock
    (![1,4,5] : Fin 3 → Fin 6) (by decide) (fun _=>0)
    (![frame bits,frame (RecoveryRadixInput.prepared bits),List.replicate (2*bits.length) false,
      List.replicate D false,[],[]] : Fin 6 → List Bool)
    (by intro i; rfl) (by intro i; fin_cases i <;> rfl)
  have B := second.congr (dockH_existing _ _ _ (by intro i; rfl))
    (HierarchyAllocation.install_eq (![1,4,5] : Fin 3 → Fin 6) (by decide) _
      (![frame bits,frame (RecoveryRadixInput.prepared bits),List.replicate (2*bits.length) false,
        List.replicate D false,RecoveryRadixInput.prepared bits,List.replicate (2*bits.length) false]) _
      (by intro i; fin_cases i <;> first | rfl | simp [RecoveryRadixInput.prepared_length])
      (by intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)))
  have all := A.seq B
  simpa only [RecoveryRadixInput.prepared_length,
    show 8*bits.length+6+1+(4*(2*bits.length)+2)=16*bits.length+9 by omega] using all

theorem signed_residue (p n : ℕ) (negative : Bool) (hp : 0<p) :
(if negative then (p - n % p) % p else n % p) =
 FinalPrimeReduce.intResidue p (if negative then -(n : Int) else (n : Int)) := by
  cases negative
  · change n % p = ((n : Int) % (p : Int)).toNat
    rw [← Int.natCast_mod]
    rfl
  · change (p - n % p) % p = FinalPrimeReduce.intResidue p (-(n : Int))
    have hr : n % p ≤ p := (Nat.mod_lt n hp).le
    have hpn : (p : Int) ≠ 0 := by exact_mod_cast hp.ne'
    apply Int.ofNat_inj.mp
    rw [Int.natCast_mod, Int.natCast_sub hr]
    unfold FinalPrimeReduce.intResidue
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hpn), Int.neg_emod_eq_sub_emod, Int.natCast_mod]
    simp only [Int.sub_emod, Int.emod_self, Int.emod_emod]

theorem native_horner (z : ℤ) :
    FinalPrimeRow.horner (RecoveryRadixInput.prepared
      (SignedSortKey.binary (natBitLength z.natAbs) z.natAbs)) (2*natBitLength z.natAbs) = z.natAbs := by
  have h := prepared_horner (SignedSortKey.binary (natBitLength z.natAbs) z.natAbs)
  rw [SignedSortKey.binary_length, SignedSortKey.binary_value] at h
  · exact h
  · exact Nat.lt_pow_succ_log_self (by decide) _

theorem native_sign (z : ℤ) :
    (if decide (z<0) then -(z.natAbs : ℤ) else (z.natAbs : ℤ))=z := by
  cases z <;> simp
  omega

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueInput
