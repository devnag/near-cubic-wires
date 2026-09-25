import Proof.Packets.PacketsXVectorLiteralProviderCall
import Proof.Packets.PacketsXWindowLiteralProviderBounded

/-! Uniform concrete provider callback for the actual vector loop. Its width
and all enumerator guards come from the real alphabet and unchanged census. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport Theorem25Completion.CycleBounds WindowNativeOrder
open CloseoutRowsRawPairSeek (cacheWord)
open WindowProvider (literalPairs)
noncomputable section

theorem literal_provider_bounded_call (C w offset W target : Nat) (codes : List Nat)
    (hc:codes.Pairwise (·<·)) (hcodes:∀c∈codes,c<C) (hsize:codes.length ≤ C)
    (hpositive:1 ≤ codes.length) (hw:3 ≤ w) (hW:W ≤ 64*(C+2)) (ho:offset ≤ 2*C) (ht:target ≤ 2*C)
    (hcount:(codes.length+1)^(2*W) ≤ 2^w)
    (left : List (List Bool)) (fields : Fin 222 → List Bool)
    (hready:ProviderReady C (commonReserve C w) fields)
    (acache:fields 152=ZeroPadding.pad (commonReserve C w) (cacheWord (literalPairs codes)))
    (hmeta:∀j : Fin 7,providerA C (commonReserve C w) left [] fields (WindowProvider.seedPorts (j.natAdd 62))=
      WindowSeed.metadata (commonReserve C w) (Nat.log 2 codes.length+1) (C+9) codes.length offset W target j) :
    ∃out,Step WindowProvider.literalProvider (WindowProvider.uniformBudget C w)
      providerH (providerA C (commonReserve C w) left [] fields)
      providerH (providerA C (commonReserve C w) left
        ((Normalized.structuralGF2ConsecutiveWindowIndicator codes offset (2*W) target).map (maskNat C)) out) ∧
      ProviderReady C (commonReserve C w) out ∧(∀j,ProviderRetained j → out j=fields j) := by
  let R:=commonReserve C w
  let v:=Nat.log 2 codes.length+1
  let A:=providerA C R left [] fields
  let T:=WindowProvider.literalProviderOutput C R v (C+9) offset W target codes A
  have core:∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left [] j:=fun j=>Fin.addCases_left j
  have run:=WindowProvider.literal_provider_bounded C w offset W target codes hc hcodes hsize hpositive hw hW ho ht hcount
    left A core acache (hready.work left []) hmeta (hready.seedWords left [])
  have shape:=provider_rebuild C R left
    ((Normalized.structuralGF2ConsecutiveWindowIndicator codes offset (2*W) target).map (maskNat C)) T
    (WindowProvider.literal_output_engine C R v (C+9) offset W target codes left A core)
  rw [←provider_window_heads] at run
  have digit:=WindowProvider.digit_width_guards codes.length
  obtain ⟨hu,hv,hM,hwidth,_hfields,_hfit,_hdfit,_htfit⟩:=
    WindowProvider.window_metadata_guards C w v codes.length W offset target (by have h:=digit.2.1;dsimp [v];omega)
      hsize hW ho ht
  have hout:=WindowProvider.emitted_private_guard C w offset W target codes hc hsize hpositive hcount
  refine ⟨(fun j=>T (j.natAdd 34)),run.congr rfl shape,
    ready_after_literal C R v (C+9) offset W target codes left fields hready hu hv (Nat.le_of_succ_le hM) hwidth hout hmeta,?_⟩
  intro j hj
  rcases hj with rfl|rfl|rfl|hj
  · change T 125=fields 91
    dsimp only [T]
    rw [WindowProvider.literal_output_middle C R v (C+9) offset W target codes A 125 (by decide) (by decide)]
    change A 125=fields 91
    exact Fin.addCases_right (91 : Fin 222)
  · change T 129=fields 95
    dsimp only [T]
    rw [WindowProvider.literal_output_middle C R v (C+9) offset W target codes A 129 (by decide) (by decide)]
    change A 129=fields 95
    exact Fin.addCases_right (95 : Fin 222)
  · change T 140=fields 106
    dsimp only [T]
    rw [WindowProvider.literal_output_middle C R v (C+9) offset W target codes A 140 (by decide) (by decide)]
    change A 140=fields 106
    exact Fin.addCases_right (106 : Fin 222)
  · exact (WindowProvider.literal_output_large C R v (C+9) offset W target codes A hmeta (j.natAdd 34)
      (by simp only [Fin.val_natAdd];omega)).trans (Fin.addCases_right j)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
