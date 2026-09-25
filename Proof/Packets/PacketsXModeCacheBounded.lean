import Proof.Packets.PacketsXModeCacheReady
import Proof.Packets.ModeCacheNumeric
import Proof.Packets.PacketsXCycleDenseAtomCost

/-! The original mode-cache producer fits the already generated common
reserve. The hash capacity is exactly the resident scalar C+9. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheBounded
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch CloseoutRowsModeCache
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
attribute [local irreducible] ModeCacheReady.machine

theorem source_budget (C w M : Nat) (p : Parameters) (hworkspace : p.C=C+9)
    (hM : M≤C) (hr : p.rank≤C) (hl : p.level≤C) : sourceBudget p M≤commonReserve C w := by
  have h:=ModeCacheNumeric.source_envelope C M p.rank p.level hM hr hl
  have he : sourceBudget p M=
      4+(M*((2*((p.rank*(5*p.rank+22)+3)+2)+2)+2*p.level+4*M+2*p.rank+2*(C+9)+55+3)+3) := by
    simp only [sourceBudget,CloseoutRowsModeCache.budget,initialState,bodyBudget,
      CloseoutRowsModeHashReady.budget,CloseoutRowsModeHashLoop.budget,hworkspace,Nat.zero_add]
  rw [he]
  exact h.trans (ModeCacheNumeric.reserve_dominates C w).1

theorem pairs_shape (C M : Nat) (mode : Fin 3) (p : Parameters) (hM : M≤C) :
    ∀a∈pairs mode p M,AtomShape C a := by
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
  have hi':i<M:=List.mem_range.mp hi
  exact ⟨_,_,i,hi'.trans_le hM,rfl⟩

theorem guards (C w M : Nat) (p : Parameters) (hworkspace : p.C=C+9)
    (hr : p.rank≤9*M) (hl : p.level≤p.rank) (hC : (258*M+2)^2≤C) :
    p.rank+2≤p.C ∧ CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C ∧
    sourceBudget p M≤commonReserve C w ∧ reuseCapacity p M≤commonReserve C w ∧
    (ModeCacheReady.word p M).length≤commonReserve C w := by
  have hM : 2*M≤C := by nlinarith only [hC,Nat.zero_le (M^2),Nat.zero_le M]
  have hrC : p.rank≤C := by nlinarith only [hC,hr,Nat.zero_le (M^2),Nat.zero_le M]
  obtain ⟨hrank,hhash⟩:=ModeCacheNumeric.hash_workspace M p.rank C hr hC
  have hs:=source_budget C w M p hworkspace (by omega) hrC (hl.trans hrC)
  have hD : reuseCapacity p M≤commonReserve C w := by
    apply le_trans (b:=3*C+13)
    · unfold reuseCapacity;rw [hworkspace];omega
    · exact (ModeCacheNumeric.reserve_dominates C w).2
  have hcount : (pairs 1 p M++pairs 2 p M).length≤C := by
    simpa [pairs, two_mul] using hM
  have hshape : ∀a∈pairs 1 p M++pairs 2 p M,AtomShape C a := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact pairs_shape C M 1 p (by omega) a ha
    · exact pairs_shape C M 2 p (by omega) a ha
  refine ⟨?_,?_,hs,hD,cache_reserve C w _ hcount hshape⟩
  · simpa only [hworkspace] using hrank
  · simpa only [hworkspace,CloseoutRowsModeHashLoop.budget] using hhash

theorem budget_reserve (C w M : Nat) (p : Parameters) (hworkspace : p.C=C+9)
    (hr : p.rank≤9*M) (hl : p.level≤p.rank) (hC : (258*M+2)^2≤C) :
    ModeCacheReady.budget p M (commonReserve C w)≤13*commonReserve C w := by
  have hs:=(guards C w M p hworkspace hr hl hC).2.2.1
  have hR:=(reserve_small C w).1
  unfold ModeCacheReady.budget ModeCacheCommon.budget
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheBounded
