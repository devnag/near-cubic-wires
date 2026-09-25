import Proof.Packets.PacketsXSubsetNormalizedOrder
import Proof.CaseAnalysis.RowsModeWindowBinomial

/-! Exact nested execution order of the frozen normalized window. The
existing ordinary coefficient workers compute the natural binomial parities.
Both inner and outer accumulators retain their separate normalized folds. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedWindow
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowBinomial

noncomputable def elementary (w : Nat) (codes : List Nat) (k : Nat) :=
  Ring.norm (SubsetOrder.reflectedSource w k codes)
noncomputable def shifted (w : Nat) (codes : List Nat) (offset degree : Nat) :=
  (List.range (degree+1)).foldl (fun acc a=>Ring.add acc
    (gf2ParityScale ((offset+(degree-a)-1).choose (degree-a)) (elementary w codes a))) []
noncomputable def window (w : Nat) (codes : List Nat) (offset width target : Nat) :=
  (List.range (width+1)).foldl (fun acc d=>Ring.add acc
    (gf2ParityScale (d.choose target) (shifted w codes offset d))) []

theorem elementary_exact (w : Nat) (codes : List Nat) (k : Nat) (hM : codes.length≤2^w) :
    elementary w codes k=Normalized.structuralGF2ElementarySymmetric codes k :=
  SubsetOrder.elementary_exact w k codes hM

theorem shifted_exact (w : Nat) (codes : List Nat) (offset degree : Nat)
    (hM : codes.length≤2^w) :
    shifted w codes offset degree=Normalized.structuralGF2ShiftedElementarySymmetric codes offset degree := by
  unfold Normalized.structuralGF2ShiftedElementarySymmetric Normalized.structuralGF2Sum
  simp only [List.Nat.antidiagonal,List.map_map,List.foldl_map]
  unfold shifted
  apply congrArg (fun f=>(List.range (degree+1)).foldl f [])
  funext acc a
  rw [elementary_exact w codes a hM]
  simp only [Function.comp_def,ringChoose_neg_natCast_castZMod,structuralGF2Scale_natCast]
  rfl

theorem window_exact (w : Nat) (codes : List Nat) (offset width target : Nat)
    (hM : codes.length≤2^w) :
    window w codes offset width target=Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target := by
  unfold Normalized.structuralGF2ConsecutiveWindowIndicator Normalized.structuralGF2Sum
  rw [List.foldl_map]
  unfold window
  apply congrArg (fun f=>(List.range (width+1)).foldl f [])
  funext acc d
  rw [shifted_exact w codes offset d hM]
  simp only [triangularCoefficient_windowDelta,structuralGF2Scale_natCast]
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedWindow
