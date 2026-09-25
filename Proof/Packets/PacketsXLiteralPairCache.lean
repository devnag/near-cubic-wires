import Proof.Packets.PacketsXLiteralPairReusable
import Proof.Packets.VectorCounterDecrement
import Proof.Packets.PhysicalRepeatStep

/-! Actual descending reflected literal cache. The counter is decremented
before every record, so the emitted numeric Nat.pair codes have exactly the
frozen reverse order, including the zero code at the end of terminal caches. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairCache
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def cachePrefix (tag count done : Nat) (pre : List Bool) := pre++
  (List.range done).flatMap (fun i=>ReflectedLiteralCache.singletonWord (Nat.pair tag (count-1-i)))
def decrement := RecoveryFocus.machine LiteralPairReusable.indexSlot VectorCounter.decrement
def body := Composition.machine decrement LiteralPairReusable.machine
def machine := RepeatMachine.machine body (fun _ _=>true)
def budget (R count : Nat) := count*(16*(R+1)+2*count+6)+3

theorem prefix_zero (tag count : Nat) (pre : List Bool) : cachePrefix tag count 0 pre=pre := by
  simp [cachePrefix]
theorem prefix_next (tag count i : Nat) (pre : List Bool) :
    cachePrefix tag count (i+1) pre=LiteralPairUnary.next tag (count-(i+1)) (cachePrefix tag count i pre) := by
  have he : count-1-i=count-(i+1) := by omega
  simp [cachePrefix,LiteralPairUnary.next,List.range_succ,List.flatMap_append,List.append_assoc,he]
theorem prefix_final (tag count : Nat) (pre : List Bool) :
    cachePrefix tag count count pre=pre++ReflectedLiteralCache.stream tag count := by
  simp [cachePrefix,ReflectedLiteralCache.stream,ReflectedLiteralCache.descending,List.flatMap_map]

theorem decrement_run (R tag index : Nat) (pre : List Bool) (hcap : index+2≤R) :
    Step decrement (2*index+4) (LiteralPairReusable.heads pre)
      (LiteralPairReusable.bank R tag (index+1) pre) (LiteralPairReusable.heads pre)
      (LiteralPairReusable.bank R tag index pre) := by
  apply PhysicalFocusBoundary.focus (VectorCounter.decrement_padded index R hcap)
    LiteralPairReusable.indexSlot (by decide)
    (LiteralPairReusable.heads pre) (LiteralPairReusable.heads pre)
    (LiteralPairReusable.bank R tag (index+1) pre) (LiteralPairReusable.bank R tag index pre)
  · intro j;fin_cases j;rfl
  · intro j;fin_cases j;rfl
  · intro j;fin_cases j;rfl
  · intro j;fin_cases j;rfl
  · intro i hi
    have hn : i≠1 := by intro h;subst i;exact hi 0 rfl
    refine ⟨rfl,?_⟩
    simp [LiteralPairReusable.bank,hn]

theorem body_run (R tag count i : Nat) (pre : List Bool) (hi : i<count)
    (hcount : count+1≤R)
    (hR : LiteralPairUnary.budget R tag (count-(i+1))+1≤R) :
    Step body (16*(R+1)+2*count+3)
      (LiteralPairReusable.heads (cachePrefix tag count i pre))
      (LiteralPairReusable.bank R tag (count-i) (cachePrefix tag count i pre))
      (LiteralPairReusable.heads (cachePrefix tag count (i+1) pre))
      (LiteralPairReusable.bank R tag (count-(i+1)) (cachePrefix tag count (i+1) pre)) := by
  have first:=decrement_run R tag (count-(i+1)) (cachePrefix tag count i pre) (by omega)
  have he : count-(i+1)+1=count-i := by omega
  rw [he] at first
  have h:=first.seq (LiteralPairReusable.run R tag (count-(i+1)) (cachePrefix tag count i pre) hR)
  rw [←prefix_next] at h
  exact h.enlarge (by unfold LiteralPairReusable.budget;omega)

theorem run (R tag count : Nat) (pre : List Bool) (hcount : count+1≤R)
    (hR : ∀ index,index<count→LiteralPairUnary.budget R tag index+1≤R) :
    Step machine (budget R count)
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat) (LiteralPairReusable.heads pre) (fun _ : Fin 1=>1))
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (LiteralPairReusable.bank R tag count pre) (fun _ : Fin 1=>CompareMachine.word count))
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat) (LiteralPairReusable.heads (pre++ReflectedLiteralCache.stream tag count)) (fun _ : Fin 1=>1))
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool) (LiteralPairReusable.bank R tag 0 (pre++ReflectedLiteralCache.stream tag count))
        (fun _ : Fin 1=>CompareMachine.word count)) := by
  have h:=PhysicalRepeatStep.run body count (16*(R+1)+2*count+3)
    (fun i=>LiteralPairReusable.heads (cachePrefix tag count i pre))
    (fun i=>LiteralPairReusable.bank R tag (count-i) (cachePrefix tag count i pre))
    (fun i hi=>body_run R tag count i pre hi hcount (hR _ (by omega)))
  simpa only [machine,budget,prefix_zero,prefix_final,Nat.sub_zero,Nat.sub_self,Nat.add_assoc] using h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairCache
