import Proof.Packets.PacketsXModeCacheBounded
import Proof.Packets.PacketsXWindowLevelAtomCost
import Proof.Packets.PacketsXWindowLevelProvider

/-! Numeric closure and a uniform paid budget for the fixed level provider.
The unchanged population square pays for hash workspace and all literal tags. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
noncomputable section

def levelUniformBudget (C w : Nat) := 2^29*(C+1)^6*2^(8*w)

theorem mode_pair_guards (C M : Nat) (p : Parameters)
    (hr : p.rank≤9*M) (hl : p.level≤p.rank) (hC : (258*M+2)^2≤C) :
    p.level+1≤C ∧ (modePairs p M).length≤C ∧
    (∀i<(modePairs p M).length,Nat.pair (p.level+1) i<C) ∧
    (∀pair∈modePairs p M,AtomShape C pair) := by
  have hM : 2*M≤C := by nlinarith only [hC,Nat.zero_le (M^2),Nat.zero_le M]
  have hlC : p.level+1≤C := by nlinarith only [hC,hl,hr,Nat.zero_le (M^2),Nat.zero_le M]
  have length : (modePairs p M).length=2*M := by simp [modePairs,pairs,two_mul]
  refine ⟨hlC,by omega,?_,?_⟩
  · intro i hi
    rw [length] at hi
    exact (LiteralAlphabet.pair_lt_square (p.level+1) i).trans_le
      ((Nat.pow_le_pow_left (by omega : p.level+1+i+1≤258*M+2) 2).trans hC)
  · intro pair hp
    rcases List.mem_append.mp hp with hp|hp
    · exact ModeCacheBounded.pairs_shape C M 1 p (by omega) pair hp
    · exact ModeCacheBounded.pairs_shape C M 2 p (by omega) pair hp

theorem level_provider_budget (C w M : Nat) (p : Parameters) (hworkspace : p.C=C+9)
    (hr : p.rank≤9*M) (hl : p.level≤p.rank) (hC : (258*M+2)^2≤C) :
    levelProviderBudget p M C (commonReserve C w)≤levelUniformBudget C w := by
  obtain ⟨htag,hcount,_,_⟩:=mode_pair_guards C M p hr hl hC
  have hmode:=ModeCacheBounded.budget_reserve C w M p hworkspace hr hl hC
  have hatoms:=level_atoms_budget C w (p.level+1) (modePairs p M).length htag hcount
  have h4 : (C+1)^4≤(C+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hreserve : commonReserve C w≤65536*(C+1)^6*2^(8*w) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 65536 h4)
  have hp : 1≤(C+1)^6*2^(8*w) := by
    simpa using Nat.mul_le_mul (Nat.one_le_pow 6 (C+1) (by omega)) (Nat.one_le_two_pow (n:=8*w))
  have hlR : p.level≤commonReserve C w := (Nat.le_of_succ_le htag).trans (Nat.le_trans (by omega) (LiteralCacheReuse.reserve_width C w))
  unfold levelProviderBudget modeAtomsBudget ModeLevelRaw.budget levelUniformBudget
  norm_num at hatoms ⊢
  nlinarith only [hmode,hatoms,hreserve,hp,hlR]

theorem level_provider_bounded (p : Parameters) (M C w : Nat)
    (out : List Bool) (priv : Fin 15 → List Bool) (initial : List PacketVector.Packet)
    (hworkspace : p.C=C+9) (hrank : p.rank≤9*M) (hl : p.level≤p.rank)
    (hC : (258*M+2)^2≤C) (hi : M≤2^p.rank) (hw : 1≤w)
    (hpriv : ∀i,(priv i).length≤commonReserve C w) (hout : out.length≤commonReserve C w)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P)
    (left right : PacketVector.Packet) (A : Fin 256 → List Bool)
    (hright : VectorAccumulator.Fits (commonReserve C w) right)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C (commonReserve C w) left right i)
    (hmode : ∀i,i≠12 → ModeCacheReady.A p M (commonReserve C w) out priv i=A (modePorts i))
    (atag : A 187=WindowSeed.source (commonReserve C w) (p.level+1))
    (acount : A 184=WindowSeed.source (commonReserve C w) (modePairs p M).length)
    (abank : A 140=PacketVector.bank (commonReserve C w) initial)
    (hprivate : ∀i,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 → (A (literalPorts i)).length≤commonReserve C w)
    (hwork : ∀i,Workspace.selected i → (A i).length≤commonReserve C w)
    (h129 : (A 129).length≤commonReserve C w)
    (h159 : (A 159).length≤commonReserve C w) (h176 : (A 176).length≤commonReserve C w) :
    Step levelProvider (levelUniformBudget C w) heads A heads
      (levelProviderOutput p M C (commonReserve C w) initial A) := by
  obtain ⟨hc,hb,hlog,hD,hword⟩:=ModeCacheBounded.guards C w M p hworkspace hrank hl hC
  obtain ⟨htag,hcount,hcodes,hshape⟩:=mode_pair_guards C M p hrank hl hC
  exact (level_provider_run p M C w out priv initial hl hc hb hi (by omega) hD hpriv hout hword
    hw htag hcount hcodes hshape hinit hinits left right A hright hengine hmode atag acount abank
    hprivate hwork h129 h159 h176).enlarge (level_provider_budget C w M p hworkspace hrank hl hC)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
