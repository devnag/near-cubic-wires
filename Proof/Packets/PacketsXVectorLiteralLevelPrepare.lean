import Proof.Packets.PacketsXVectorLiteralLevelFields
import Proof.Packets.PacketsXWindowLevelProviderBounded
import Proof.Packets.PacketsXWindowLevelProviderLayout
import Proof.Packets.PacketsXVectorLiteralProviderCall

/-! The actual level-controller join. Resident numeric counters produce the
new window and successor tag before the fixed cache/atom provider runs.
No preparation or cache execution theorem is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache Theorem25Completion.CycleBounds
noncomputable section

def literalLevelOutput (p : Parameters) (M C R root : Nat) (initial : List PacketVector.Packet)
    (left right : PacketVector.Packet) (fields : Fin 222 → List Bool) :=
  WindowProvider.levelProviderOutput p M C R initial (providerA C R left right (levelFields R root p.level fields))

theorem literal_level_prepare_run (p : Parameters) (M C w ci pi root old : Nat)
    (out : List Bool) (priv : Fin 15 → List Bool) (initial : List PacketVector.Packet)
    (hworkspace : p.C=C+9) (hrank : p.rank≤9*M) (hl : p.level≤p.rank)
    (hC : (258*M+2)^2≤C) (hi : M≤2^p.rank) (hw : 1≤w)
    (hpriv : ∀i,(priv i).length≤commonReserve C w) (hout : out.length≤commonReserve C w)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P)
    (left right : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (hright : VectorAccumulator.Fits (commonReserve C w) right)
    (hready : ProviderReady C (commonReserve C w) fields)
    (hin : ∀j,A C (commonReserve C w) ci pi p.level left right [] previous next fields extra (VectorWorkerArena.windowSlots j)=
      GradedWindow.A (commonReserve C w) root p.level 0 0 old j)
    (hroot : root+67≤commonReserve C w) (hold : old+1≤commonReserve C w)
    (htag : (fields 153).length=commonReserve C w)
    (hmode : ∀i,i≠12 → ModeCacheReady.A p M (commonReserve C w) out priv i=
      providerA C (commonReserve C w) left right fields (WindowProvider.modePorts i))
    (acount : fields 150=WindowSeed.source (commonReserve C w) (WindowProvider.modePairs p M).length)
    (abank : fields 106=PacketVector.bank (commonReserve C w) initial)
    (hprivate : ∀i,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 →
      (providerA C (commonReserve C w) left right fields (WindowProvider.literalPorts i)).length≤commonReserve C w)
    (h129 : (fields 95).length≤commonReserve C w)
    (h159 : (fields 125).length≤commonReserve C w) (h176 : (fields 142).length≤commonReserve C w) :
    Step (prepareLevel WindowProvider.levelProvider)
      (prepareBudget (commonReserve C w) root p.level (WindowProvider.levelUniformBudget C w))
      (H (fun _=>0)) (A C (commonReserve C w) ci pi p.level left right [] previous next fields extra)
      (H (fun _=>0)) (A C (commonReserve C w) ci pi p.level left [] [] previous next
        (fun j=>literalLevelOutput p M C (commonReserve C w) root initial left right fields (j.natAdd 34)) extra) ∧
    ProviderReady C (commonReserve C w)
      (fun j=>literalLevelOutput p M C (commonReserve C w) root initial left right fields (j.natAdd 34)) := by
  let R:=commonReserve C w
  let f:=levelFields R root p.level fields
  let B:=providerA C R left right f
  have engine : ∀j : Fin 34,B (j.castAdd 222)=ReusableArithmetic.state C R left right j := fun j=>Fin.addCases_left j
  have kept (i : Fin 256) (h152 : i≠152) (h187 : i≠187) : B i=providerA C R left right fields i :=
    provider_level_fields_other C R root p.level left right fields i h152 h187
  have tagB : B 187=WindowSeed.source R (p.level+1) := by
    change f 153=_
    simp only [f,levelFields,Function.update_self]
    rfl
  have countB : B 184=WindowSeed.source R (WindowProvider.modePairs p M).length :=
    (kept 184 (by decide) (by decide)).trans acount
  have readyF : ProviderReady C R f := ready_level_fields C R root p.level fields hready
  obtain ⟨htagC,hcountC,_,_⟩:=WindowProvider.mode_pair_guards C M p hrank hl hC
  have reserve : C+2≤R := LiteralCacheReuse.reserve_width C w
  have provider := WindowProvider.level_provider_bounded p M C w out priv initial hworkspace hrank hl hC hi hw
    hpriv hout hinit hinits left right B hright engine
    (by
      intro i hi
      have away : ∀j,WindowProvider.modePorts j≠152 ∧ WindowProvider.modePorts j≠187 := by decide
      rw [kept _ (away i).1 (away i).2]
      exact hmode i hi)
    tagB countB ((kept 140 (by decide) (by decide)).trans abank)
    (by
      intro i h59 h60 h62 h64 h65
      have away : ∀j : Fin 68,j≠64 → WindowProvider.literalPorts j≠152 ∧ WindowProvider.literalPorts j≠187 := by decide
      rw [kept _ (away i h64).1 (away i h64).2]
      exact hprivate i h59 h60 h62 h64 h65)
    (readyF.work left right)
    (by rw [kept 129 (by decide) (by decide)];exact h129)
    (by rw [kept 159 (by decide) (by decide)];exact h159)
    (by rw [kept 176 (by decide) (by decide)];exact h176)
  rw [←provider_window_heads] at provider
  have outputCore:= (WindowProvider.level_output_layout p M C R initial left right B (by omega)
    engine tagB countB (by omega) (by omega)).1
  refine ⟨prepare_level_right_run WindowProvider.levelProvider C R ci pi p.level root old
    (WindowProvider.levelUniformBudget C w) left right [] previous next fields extra
    (literalLevelOutput p M C R root initial left right fields) hin hroot (by omega) hold htag provider outputCore,?_⟩
  exact WindowProvider.level_output_provider_ready p M C R initial left right f (by omega) readyF
    tagB countB (by omega) (by omega)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
