import Proof.Packets.PacketsXVectorProviderReady

/-! The concrete literal-window provider at the canonical controller
boundary, with reusable capacity and all retained numeric masters restored. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport Theorem25Completion.CycleBounds WindowNativeOrder
open CloseoutRowsRawPairSeek (cacheWord)
open WindowProvider (literalPairs)
noncomputable section

theorem provider_window_heads : providerH=WindowProvider.heads := by
  funext i
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · simp only [providerH,Fin.addCases_left,ReusableArithmetic.heads,WindowProvider.heads,Fin.ext_iff,Fin.val_castAdd]
    rfl
  · have hn:j.natAdd 34≠(31 : Fin 256):=by
      intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
    simp only [providerH,Fin.addCases_right,WindowProvider.heads,if_neg hn]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
