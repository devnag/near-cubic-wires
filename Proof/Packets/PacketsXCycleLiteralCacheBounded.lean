import Proof.Packets.PacketsXCycleLiteralPairCost
import Proof.Packets.PacketsXLiteralPairCache

/-! A concrete reflected-cache run with every scratch/fuel guard discharged
by the physically generated common reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleLiteralPairCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed.Materializer

theorem commonReserve_scalar (C w : Nat) : C+1≤commonReserve C w := by
  have he : 1≤2^(8*w) := Nat.one_le_pow _ _ (by decide)
  have hp : C+1≤(C+1)^4 := by
    have h := Nat.pow_le_pow_right (show 1≤C+1 by omega) (show 1≤4 by omega)
    simpa using h
  unfold commonReserve CycleCommonReserve.reserve
  nlinarith [Nat.mul_le_mul_left (65536*(C+1)^4) he]

theorem cache_run (C w tag count : Nat) (pre : List Bool)
    (htag : tag≤C) (hcount : count≤C) (hcode : ∀ index,index<count→Nat.pair tag index≤C) :
    let R:=commonReserve C w
    Step LiteralPairCache.machine (LiteralPairCache.budget R count)
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat) (LiteralPairReusable.heads pre) (fun _ : Fin 1=>1))
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (LiteralPairReusable.bank R tag count pre) (fun _ : Fin 1=>CompareMachine.word count))
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat) (LiteralPairReusable.heads (pre++ReflectedLiteralCache.stream tag count)) (fun _ : Fin 1=>1))
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (LiteralPairReusable.bank R tag 0 (pre++ReflectedLiteralCache.stream tag count))
        (fun _ : Fin 1=>CompareMachine.word count)) := by
  dsimp only
  apply LiteralPairCache.run
  · exact (Nat.add_le_add_right hcount 1).trans (commonReserve_scalar C w)
  · intro index hi
    exact budget_reserve _ C w tag index htag (by omega) (hcode index hi)

end Theorem25Completion.CycleLiteralPairCost
