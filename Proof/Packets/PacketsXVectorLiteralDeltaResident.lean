import Proof.Packets.PacketsXVectorLiteralDeltaRun
import Proof.Packets.PacketsXCycleDeltaMetadataCost

/-! A reentrant concrete delta call from resident numeric masters. The
actual counter layout and every numeric bound are discharged here; neither
metadata execution nor literal-window execution is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open Theorem25Completion Theorem25Completion.CycleBounds
noncomputable section

structure LiteralDeltaResident (C R n W : Nat) (codes : List Nat) (fields : Fin 222 → List Bool) : Prop where
  ready : ProviderReady C R fields
  childCount : fields 116=WindowSeed.source R n
  window : fields 118=WindowSeed.source R W
  width : fields 149=WindowSeed.source R (C+9)
  count : fields 150=WindowSeed.source R codes.length
  digit : fields 151=WindowSeed.source R (Nat.log 2 codes.length+1)
  cache : fields 152=ZeroPadding.pad R (CloseoutRowsRawPairSeek.cacheWord (WindowProvider.literalPairs codes))

theorem resident_metadata_input (C R n W ci pi li : Nat) (codes : List Nat)
    (left right acc : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralDeltaResident C R n W codes fields)
    (hcold : ∀j,j.val<17 → extra j=List.replicate R false) :
    ∀j,j≠11 → j≠12 → j≠21 →
      A C R ci pi li left right acc previous next fields extra (VectorWorkerArena.metadataSlots j)=
        DeltaScalarFields.input R (C+9) n W pi ci j := by
  intro j h11 h12 h21
  fin_cases j
  · exact h.childCount
  · exact h.window
  · rfl
  · rfl
  · exact h.width
  · exact hcold 0 (by decide)
  · exact hcold 1 (by decide)
  · exact hcold 2 (by decide)
  · exact hcold 3 (by decide)
  · exact hcold 4 (by decide)
  · exact hcold 5 (by decide)
  · contradiction
  · contradiction
  · exact hcold 6 (by decide)
  · exact hcold 7 (by decide)
  · exact hcold 8 (by decide)
  · exact hcold 9 (by decide)
  · exact hcold 10 (by decide)
  · exact hcold 11 (by decide)
  · exact hcold 12 (by decide)
  · exact hcold 13 (by decide)
  · contradiction
  · exact hcold 14 (by decide)
  · exact hcold 15 (by decide)
  · exact hcold 16 (by decide)

def literalDeltaFuel (C w : Nat) := 2^42*(C+1)^6*2^(8*w)

theorem literal_delta_fuel (C w n W pi ci : Nat) (hn : n≤C) (hp : pi≤C) (hc : ci≤C)
    (hW : W≤64*(C+2)) :
    12*commonReserve C w+DeltaMetadata.budget (C+9) n W pi ci+WindowProvider.uniformBudget C w+27≤
      literalDeltaFuel C w := by
  have hm : DeltaMetadata.budget (C+9) n W pi ci+1≤commonReserve C w :=
    CycleDeltaMetadataCost.budget_reserve C w n W pi ci hn hp hc hW
  have h4 : (C+1)^4≤(C+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hr : commonReserve C w≤65536*(C+1)^6*2^(8*w) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 65536 h4)
  have he : 1≤(C+1)^6*2^(8*w) := by
    simpa using Nat.mul_le_mul (Nat.one_le_pow 6 (C+1) (by omega)) (Nat.one_le_two_pow (n:=8*w))
  unfold WindowProvider.uniformBudget literalDeltaFuel
  norm_num
  nlinarith only [hm,hr,he]

theorem literal_delta_resident_run (C w n W ci pi li : Nat) (codes : List Nat)
    (hc : codes.Pairwise (·<·)) (hcodes : ∀c∈codes,c<C) (hsize : codes.length≤C)
    (hpositive : 1≤codes.length) (hw : 3≤w) (hW : W≤64*(C+2))
    (hcount : (codes.length+1)^(2*W)≤2^w) (hn : n≤C) (hpi : pi≤C) (hci : ci≤C)
    (left right acc : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralDeltaResident C (commonReserve C w) n W codes fields)
    (hr : VectorAccumulator.Fits (commonReserve C w) right)
    (hcold : ∀j,j.val<17 → extra j=List.replicate (commonReserve C w) false) :
    ∃out,Step (delta WindowProvider.literalProvider) (literalDeltaFuel C w)
      (H (fun _=>0)) (A C (commonReserve C w) ci pi li left right acc previous next fields extra)
      (H (fun _=>0)) (A C (commonReserve C w) ci pi li left
        (deltaPacket n W pi ci (literalWindowPacket C codes (n-W) W)) acc previous next out extra) ∧
      LiteralDeltaResident C (commonReserve C w) n W codes out ∧
      (∀j,ProviderRetained j → j≠146 → j≠147 → j≠148 → out j=fields j) := by
  have scalar:=CycleWindowScalars.scalar_guards C n pi ci W hn hpi hci hW
  have reserve : 28*(C+9)+35≤commonReserve C w := CycleWindowScalars.reserve_guard C w
  have budget : DeltaMetadata.budget (C+9) n W pi ci+1≤commonReserve C w :=
    CycleDeltaMetadataCost.budget_reserve C w n W pi ci hn hpi hci hW
  obtain ⟨out,run,ready,kept⟩:=literal_delta_run C w n W ci pi li codes hc hcodes hsize hpositive hw hW hcount hn hpi
    left right acc previous next fields extra h.ready hr (by omega) (by omega) hcold
    (resident_metadata_input C _ n W ci pi li codes left right acc previous next fields extra h hcold)
    scalar.1 scalar.2.1 scalar.2.2.1 scalar.2.2.2 (by exact reserve) (by omega) budget
    h.cache h.width h.count h.digit h.window
  refine ⟨out,run.enlarge (literal_delta_fuel C w n W pi ci hn hpi hci hW),?_,kept⟩
  refine ⟨ready,?_,?_,?_,?_,?_,?_⟩
  · exact (kept 116 (by unfold ProviderRetained;decide) (by decide) (by decide) (by decide)).trans h.childCount
  · exact (kept 118 (by unfold ProviderRetained;decide) (by decide) (by decide) (by decide)).trans h.window
  · exact (kept 149 (by unfold ProviderRetained;decide) (by decide) (by decide) (by decide)).trans h.width
  · exact (kept 150 (by unfold ProviderRetained;decide) (by decide) (by decide) (by decide)).trans h.count
  · exact (kept 151 (by unfold ProviderRetained;decide) (by decide) (by decide) (by decide)).trans h.digit
  · exact (kept 152 (by unfold ProviderRetained;decide) (by decide) (by decide) (by decide)).trans h.cache

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
