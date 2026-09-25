import Proof.Packets.PacketsXWindowNativeOrder
import Proof.Packets.PacketsXWindowSourceBounds

/-! Exact source-coordinate and degree guards for the executed positional
window. These supply the original raw singleton substitution consumer. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowNativeOrder
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary.RowTupleSubsets
open NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowBinomial

theorem mem_scale (n : Nat) (P : Ring.Poly Nat) (m : List Nat) (h : m∈gf2ParityScale n P) : m∈P := by
  unfold gf2ParityScale at h
  split at h
  · simp at h
  · exact h

theorem shifted_bounds (v M offset d : Nat) (hM : M≤2^v) (m : List Nat)
    (hm : m∈positionalShifted v M offset d) : m.length≤d ∧ ∀i∈m,i<M := by
  obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp hm
  have hs:=(selected_mem v M (d-j) hM m).mp (mem_scale _ _ _ hm)
  obtain ⟨hsub,hlen⟩:=List.mem_sublistsLen.mp hs
  refine ⟨by omega,?_⟩
  intro i hi
  exact List.mem_range.mp (hsub.subset hi)

theorem window_bounds (v M offset width target : Nat) (hM : M≤2^v) (m : List Nat)
    (hm : m∈positionalWindow v M offset width target) : m.length≤width ∧ ∀i∈m,i<M := by
  obtain ⟨d,hd,hm⟩:=List.mem_flatMap.mp hm
  have h:=shifted_bounds v M offset d hM m (mem_scale _ _ _ hm)
  have hdw:=List.mem_range.mp hd
  exact ⟨by omega,h.2⟩

theorem positional_length (codes : List Nat) (hc : codes.Pairwise (·<·))
    (v offset width target : Nat) (hM : codes.length≤2^v) :
    (positionalWindow v codes.length offset width target).length≤(width+1)*(codes.length+1)^width := by
  have h:=WindowHomogeneousOrder.nativeWindow_length_sharp codes hc v offset width target hM
  rw [←reflected_window] at h
  simpa only [List.length_map] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowNativeOrder
