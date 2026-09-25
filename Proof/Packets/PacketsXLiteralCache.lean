import Proof.Packets.PacketsXLiteralCacheAllocate
import Proof.Packets.PacketsXCycleLiteralCacheBounded
import Proof.Packets.PhysicalBoundedLeftRewind

/-! Complete cold reflected singleton cache: allocate all scratch and loop
drivers, construct codes in the exact descending order, then physically
return the emitted cache cursor to zero. Only actual raw R and the actual
unary tag/count templates are supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Theorem25Completion Theorem25Completion.CycleLiteralPairCost Completion
noncomputable section

def slots : Fin 2→Fin 68 := ![62,2]
def loop := TapeEmbedding.machine 6 LiteralPairCache.machine
def rewind := RecoveryFocus.machine slots PhysicalBoundedLeftRewind.machine
def budget (R tag count : Nat) := LiteralCacheAllocate.budget R tag count+1+
  LiteralPairCache.budget R count+1+(2*R+2)

theorem stream_length (C tag count : Nat) (hcode : ∀ i,i<count→Nat.pair tag i≤C) :
    (ReflectedLiteralCache.stream tag count).length≤count*(C+6) := by
  have flat_bound (codes : List Nat) (hc : ∀ code∈codes,code≤C) :
      (codes.flatMap ReflectedLiteralCache.singletonWord).length≤codes.length*(C+6) := by
    induction codes with
    | nil => simp
    | cons x xs ih =>
      have hh:=hc x (by simp)
      have ht:=ih (by intro y hy;exact hc y (by simp [hy]))
      simp only [List.flatMap_cons,List.length_append,ReflectedLiteralCache.singletonWord_length,
        List.length_cons]
      nlinarith
  have h:=flat_bound (ReflectedLiteralCache.descending tag count) (by
    intro code hc
    rcases List.mem_map.mp hc with ⟨i,hi,rfl⟩
    have hi':i<count := List.mem_range.mp hi
    exact hcode _ (by omega))
  simpa [ReflectedLiteralCache.stream,ReflectedLiteralCache.descending] using h

theorem stream_reserve (C w tag count : Nat) (hc : count≤C)
    (hcode : ∀ i,i<count→Nat.pair tag i≤C) :
    (ReflectedLiteralCache.stream tag count).length≤commonReserve C w := by
  have hl:=(stream_length C tag count hcode).trans (Nat.mul_le_mul_right (C+6) hc)
  have hp : (C+1)^2≤(C+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have he : 1≤2^(8*w) := Nat.one_le_pow _ _ (by decide)
  unfold commonReserve CycleCommonReserve.reserve
  nlinarith [Nat.mul_le_mul_left (65536*(C+1)^4) he]


end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheCold
