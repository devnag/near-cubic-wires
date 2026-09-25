import Proof.Packets.PacketsXVectorWorkerDeltaRound
import Proof.Packets.PacketsXVectorLiteralProviderBounded

/-! The actual per-child literal delta transaction. The provider execution
premise of the generic controller is instantiated by the fixed literal
provider, including numeric metadata replacement and physical cleanup. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
open CloseoutRowsRawPairSeek (cacheWord)
noncomputable section

def literalWindowPacket (C : Nat) (codes : List Nat) (offset W target : Nat) :=
  (Normalized.structuralGF2ConsecutiveWindowIndicator codes offset (2*W) target).map (maskNat C)

theorem literal_delta_run (C w n W ci pi li : Nat) (codes : List Nat)
    (hc : codes.Pairwise (·<·)) (hcodes : ∀c∈codes,c<C) (hsize : codes.length ≤ C)
    (hpositive : 1 ≤ codes.length) (hw : 3 ≤ w) (hW : W ≤ 64*(C+2))
    (hcount : (codes.length+1)^(2*W) ≤ 2^w) (hnC : n ≤ C) (hpiC : pi ≤ C)
    (left right acc : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (hready : ProviderReady C (commonReserve C w) fields)
    (hr : VectorAccumulator.Fits (commonReserve C w) right)
    (hRpositive : 1 ≤ commonReserve C w) (huR : 2*(C+9)+1 ≤ commonReserve C w)
    (hcold : ∀j,j.val<17 → extra j=List.replicate (commonReserve C w) false)
    (hin : ∀j,j≠11 → j≠12 → j≠21 → 
      A C (commonReserve C w) ci pi li left right acc previous next fields extra (VectorWorkerArena.metadataSlots j)=
        DeltaScalarFields.input (commonReserve C w) (C+9) n W pi ci j)
    (hn : n<2^(C+9)) (hsum : min n W+pi<2^(C+9)) (hci : 2*ci<2^(C+9)) (hwidth : 2*W<2^(C+9))
    (hR : DeltaTargetGuard.budget (C+9)+1 ≤ commonReserve C w) (hN : n+2 ≤ commonReserve C w)
    (hbudget : DeltaMetadata.budget (C+9) n W pi ci+1 ≤ commonReserve C w)
    (acache : fields 152=ZeroPadding.pad (commonReserve C w) (cacheWord (WindowProvider.literalPairs codes)))
    (au : fields 149=WindowSeed.source (commonReserve C w) (C+9))
    (aM : fields 150=WindowSeed.source (commonReserve C w) codes.length)
    (av : fields 151=WindowSeed.source (commonReserve C w) (Nat.log 2 codes.length+1))
    (aW : fields 118=WindowSeed.source (commonReserve C w) W) :
    ∃out,Step (delta WindowProvider.literalProvider)
      (12*commonReserve C w+DeltaMetadata.budget (C+9) n W pi ci+WindowProvider.uniformBudget C w+27)
      (H (fun _=>0)) (A C (commonReserve C w) ci pi li left right acc previous next fields extra)
      (H (fun _=>0)) (A C (commonReserve C w) ci pi li left
        (deltaPacket n W pi ci (literalWindowPacket C codes (n-W) W)) acc previous next out extra) ∧
      ProviderReady C (commonReserve C w) out ∧
      (∀j,ProviderRetained j → j≠146 → j≠147 → j≠148 → out j=fields j) := by
  let R:=commonReserve C w
  have field_length (x : Nat) : (DeltaScalarFields.fw R (C+9) x).length=R := by
    simp only [DeltaScalarFields.fw,ZeroPadding.pad_length,frame_length,SignedSortKey.binary_length]
    exact Nat.max_eq_left huR
  apply delta_round_run WindowProvider.literalProvider C R (C+9) n W ci pi li
    (WindowProvider.uniformBudget C w) left right acc previous next fields extra
    (literalWindowPacket C codes (n-W) W)
    (fun f=>ProviderReady C R f ∧ ∀j,ProviderRetained j → j≠146 → j≠147 → j≠148 → f j=fields j)
    hr hRpositive hready.frame180 hready.frame181 hready.frame182 hcold hin hn hsum hci hwidth hR hN hbudget
  · intro f f180 f181 f182 retained
    refine ⟨ready_after_metadata C R fields f hready retained ?_ ?_ ?_,?_⟩
    · rw [f180];exact field_length _
    · rw [f181];exact field_length _
    · rw [f182];exact field_length _
    · intro j _ h146 h147 h148;exact retained j h146 h147 h148
  · intro target f ht f180 f181 f182 retained
    have ready : ProviderReady C R f := ready_after_metadata C R fields f hready retained
      (by rw [f180];exact field_length _) (by rw [f181];exact field_length _) (by rw [f182];exact field_length _)
    have target_le : target ≤ 2*C := by
      rw [NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdOneHotTargetArithmetic.target_option] at ht
      split at ht
      · split at ht
        · cases ht;omega
        · contradiction
      · contradiction
    have hmeta : ∀j : Fin 7,providerA C R left [] f (WindowProvider.seedPorts (j.natAdd 62))=
        WindowSeed.metadata R (Nat.log 2 codes.length+1) (C+9) codes.length (n-W) W target j := by
      intro j
      fin_cases j
      · exact f180
      · exact f181
      · exact f182
      · exact (retained 149 (by decide) (by decide) (by decide)).trans au
      · exact (retained 150 (by decide) (by decide) (by decide)).trans aM
      · exact (retained 151 (by decide) (by decide) (by decide)).trans av
      · exact (retained 118 (by decide) (by decide) (by decide)).trans aW
    obtain ⟨out,run,hout,kept⟩:=literal_provider_bounded_call C w (n-W) W target codes hc hcodes hsize hpositive
      hw hW (by omega) target_le hcount left f ready
      ((retained 152 (by decide) (by decide) (by decide)).trans acache) hmeta
    refine ⟨out,run,hout,?_⟩
    intro j hj h146 h147 h148
    exact (kept j hj).trans (retained j h146 h147 h148)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
