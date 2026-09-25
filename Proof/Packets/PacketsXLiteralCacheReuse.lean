import Proof.Packets.PacketsXLiteralCacheReload

/-! Reentry of the reflected-cache provider. The previous cache and all
private backing are physically cleared, metadata is reloaded from retained
actual templates, and the new exact stream is returned at cursor zero. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheReuse
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization Completion
open Theorem25Completion Theorem25Completion.CycleLiteralPairCost
noncomputable section

def pads (R : Nat) (i : Fin 62) : Nat := if i=2 ∨ i=61 then R else 0
def extra (R tag count : Nat) : Fin 6→List Bool :=
  ![UnaryTemplate.tape R,List.replicate R false,UnaryTemplate.tape tag,
    UnaryTemplate.tape count,List.replicate R false,List.replicate R false]
def output (R tag count : Nat) (i : Fin 68) : List Bool :=
  if i=2 then ZeroPadding.pad R (ReflectedLiteralCache.stream tag count)
  else if i=1 then UWalkUnary.source R 0 else LiteralCacheReload.ready R tag count i
def middleHeads (tag count : Nat) (i : Fin 68) : Nat :=
  if i=2 then (ReflectedLiteralCache.stream tag count).length else LiteralCacheReload.heads i
abbrev heads:=LiteralCacheReload.heads
abbrev loop:=LiteralCacheCold.loop
abbrev rewind:=LiteralCacheCold.rewind
def machine:=Composition.machine (Composition.machine LiteralCacheReload.machine loop) rewind
def budget (R tag count : Nat):=LiteralCacheReload.budget R tag count+1+LiteralPairCache.budget R count+1+(2*R+2)

theorem ready_eq (R tag count : Nat) : LiteralCacheReload.ready R tag count=
    Fin.addCases (m:=62) (n:=6) (motive:=fun _=>List Bool)
      (fun i=>ZeroPadding.pad (pads R i)
        (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool)
          (LiteralPairReusable.bank R tag count []) (fun _=>CompareMachine.word count) i))
      (extra R tag count) := by
  have hz : ZeroPadding.pad R []=List.replicate R false:=by simp [ZeroPadding.pad]
  funext i;fin_cases i <;>
    simp [LiteralCacheReload.ready,LiteralCacheReload.bank4,LiteralCacheReload.bank3,
      LiteralCacheReload.cleared,LiteralCacheReload.input,pads,extra,LiteralPairReusable.bank,
      Fin.addCases,ZeroPadding.pad_zero,hz,UWalkUnary.source]

theorem output_eq (R tag count : Nat) : output R tag count=
    Fin.addCases (m:=62) (n:=6) (motive:=fun _=>List Bool)
      (fun i=>ZeroPadding.pad (pads R i)
        (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>List Bool)
          (LiteralPairReusable.bank R tag 0 (ReflectedLiteralCache.stream tag count))
          (fun _=>CompareMachine.word count) i)) (extra R tag count) := by
  funext i;fin_cases i <;>
    simp [output,LiteralCacheReload.ready,LiteralCacheReload.bank4,LiteralCacheReload.bank3,
      LiteralCacheReload.cleared,LiteralCacheReload.input,pads,extra,LiteralPairReusable.bank,
      Fin.addCases,ZeroPadding.pad_zero,UWalkUnary.source]

theorem heads_eq : heads=Fin.addCases (m:=62) (n:=6) (motive:=fun _=>Nat)
    (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat) (LiteralPairReusable.heads []) (fun _=>1))
    LiteralCacheAllocate.extraHeads := LiteralCacheAllocate.heads_eq

theorem middleHeads_eq (tag count : Nat) : middleHeads tag count=
    Fin.addCases (m:=62) (n:=6) (motive:=fun _=>Nat)
      (Fin.addCases (m:=61) (n:=1) (motive:=fun _=>Nat)
        (LiteralPairReusable.heads (ReflectedLiteralCache.stream tag count)) (fun _=>1))
      LiteralCacheAllocate.extraHeads := by
  funext i;fin_cases i <;>rfl

theorem loop_run (C w tag count : Nat) (ht : tag≤C) (hc : count≤C)
    (hcode : ∀ i,i<count→Nat.pair tag i≤C) :
    let R:=commonReserve C w
    Step loop (LiteralPairCache.budget R count) heads (LiteralCacheReload.ready R tag count)
      (middleHeads tag count) (output R tag count) := by
  let R:=commonReserve C w
  have h:=((CycleLiteralPairCost.cache_run C w tag count [] ht hc hcode).pad (pads R)).embed
    LiteralCacheAllocate.extraHeads (extra R tag count)
  simp only [List.nil_append] at h
  exact (h.congr_in heads_eq.symm (ready_eq R tag count).symm).congr
    (middleHeads_eq tag count).symm (output_eq R tag count).symm

theorem rewind_run (R tag count : Nat) (hs : (ReflectedLiteralCache.stream tag count).length≤R) :
    Step rewind (2*R+2) (middleHeads tag count) (output R tag count) heads (output R tag count) := by
  obtain ⟨r,hr,hf,hn⟩:=PhysicalBoundedLeftRewind.run R
    (ReflectedLiteralCache.stream tag count).length
    (ZeroPadding.pad R (ReflectedLiteralCache.stream tag count)) hs
  have small : Step PhysicalBoundedLeftRewind.machine (2*R+2)
      ![1,(ReflectedLiteralCache.stream tag count).length]
      ![UnaryTemplate.tape R,ZeroPadding.pad R (ReflectedLiteralCache.stream tag count)]
      ![1,0] ![UnaryTemplate.tape R,ZeroPadding.pad R (ReflectedLiteralCache.stream tag count)] :=
    ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hn.le⟩
  apply PhysicalFocusBoundary.focus small LiteralCacheCold.slots (by decide)
    (middleHeads tag count) heads (output R tag count) (output R tag count)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi
    have h2 : i≠2:=fun h=>hi 1 h.symm
    exact ⟨by simp [middleHeads,h2],rfl⟩

theorem reserve_width (C w : Nat) : C+2≤commonReserve C w := by
  have he : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
  have hp : C+1≤(C+1)^4:=Nat.le_self_pow (by decide) _
  unfold commonReserve CycleCommonReserve.reserve
  nlinarith [Nat.mul_le_mul_left (65536*(C+1)^4) he]

theorem run (C w tag count : Nat) (b : Fin 68→List Bool) (ht : tag≤C) (hc : count≤C)
    (hcode : ∀ i,i<count→Nat.pair tag i≤C)
    (hb : ∀ i,i≠59→i≠60→i≠62→i≠64→i≠65→(b i).length≤commonReserve C w) :
    let R:=commonReserve C w
    Step machine (budget R tag count) heads (LiteralCacheReload.input R tag count b)
      heads (output R tag count) := by
  have hR:=reserve_width C w
  exact ((LiteralCacheReload.run (commonReserve C w) tag count b (by omega) (by omega) hb).seq
    (loop_run C w tag count ht hc hcode)).seq
    (rewind_run _ tag count (LiteralCacheCold.stream_reserve C w tag count hc hcode))

/-- Retained tag/count templates may already have physical zero backing.
The same executed provider preserves it; no fresh metadata tapes are required. -/
theorem run_metadata_pad (C w tag count tagBacking countBacking : Nat)
    (b : Fin 68→List Bool) (ht : tag≤C) (hc : count≤C)
    (hcode : ∀ i,i<count→Nat.pair tag i≤C)
    (hb : ∀ i,i≠59→i≠60→i≠62→i≠64→i≠65→(b i).length≤commonReserve C w) :
    let R:=commonReserve C w
    let p : Fin 68→Nat:=fun i=>if i=64 then tagBacking else if i=65 then countBacking else 0
    Step machine (budget R tag count) heads
      (fun i=>ZeroPadding.pad (p i) (LiteralCacheReload.input R tag count b i))
      heads (fun i=>ZeroPadding.pad (p i) (output R tag count i)) :=
  (run C w tag count b ht hc hcode hb).pad _

theorem output_private_lengths (C w tag count : Nat) (ht : tag≤C) (hc : count≤C)
    (hcode : ∀ i,i<count→Nat.pair tag i≤C) :
    ∀ i,i≠59→i≠60→i≠62→i≠64→i≠65→(output (commonReserve C w) tag count i).length=commonReserve C w := by
  have hR:=reserve_width C w
  have hs:=LiteralCacheCold.stream_reserve C w tag count hc hcode
  have ht2 : tag+2≤commonReserve C w:=by omega
  have hc2 : count+2≤commonReserve C w:=by omega
  have ht' : tag+1≤commonReserve C w:=by omega
  have hc' : count+1≤commonReserve C w:=by omega
  have h1 : 1≤commonReserve C w:=by omega
  intro i h59 h60 h62 h64 h65
  fin_cases i <;>simp_all [output,LiteralCacheReload.ready,LiteralCacheReload.bank4,
    LiteralCacheReload.bank3,LiteralCacheReload.cleared,LiteralCacheReload.input,
    UWalkUnary.source,ZeroPadding.pad_length,CompareMachine.word,Nat.max_eq_left]


end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheReuse
