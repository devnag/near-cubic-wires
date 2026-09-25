import Proof.Packets.PacketsXWindowPositionalBounds

/-! Every positional monomial is an actual subset of the runtime population.
Consequently even an oversized degree parameter never produces a long native
monomial beyond the population bound. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowNativeOrder
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary.RowTupleSubsets

theorem shifted_sublist (v M offset d : Nat) (hM : M≤2^v) (m : List Nat)
    (hm : m∈positionalShifted v M offset d) : m.Sublist (List.range M) := by
  obtain ⟨j,_,hm⟩:=List.mem_flatMap.mp hm
  exact (List.mem_sublistsLen.mp ((selected_mem v M (d-j) hM m).mp (mem_scale _ _ _ hm))).1

theorem window_sublist (v M offset width target : Nat) (hM : M≤2^v) (m : List Nat)
    (hm : m∈positionalWindow v M offset width target) : m.Sublist (List.range M) := by
  obtain ⟨d,_,hm⟩:=List.mem_flatMap.mp hm
  exact shifted_sublist v M offset d hM m (mem_scale _ _ _ hm)

theorem window_monomial_length (v M offset width target : Nat) (hM : M≤2^v) (m : List Nat)
    (hm : m∈positionalWindow v M offset width target) : m.length≤M := by
  simpa only [List.length_range] using (window_sublist v M offset width target hM m hm).length_le

theorem window_raw_count (codes : List Nat) (hc : codes.Pairwise (·<·))
    (v offset width target w : Nat) (hM : codes.length≤2^v)
    (hdegree : width+1≤2^w) (hcount : (codes.length+1)^width≤2^w) :
    (positionalWindow v codes.length offset width target).length≤2^(2*w) := by
  have h:=(positional_length codes hc v offset width target hM).trans (Nat.mul_le_mul hdegree hcount)
  simpa only [←pow_add,show w+w=2*w by omega] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowNativeOrder
