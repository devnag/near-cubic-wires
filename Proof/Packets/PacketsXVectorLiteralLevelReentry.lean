import Proof.Packets.PacketsXVectorLiteralLevelState
import Proof.Packets.PacketsXWindowLevelProviderReentry

/-! The fixed preparation produces the entire next-entry data invariant,
with the actual cumulative dense table. Parent iteration preserves this
invariant by retaining its masters and restoring the work capacities. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache Theorem25Completion.CycleBounds
noncomputable section

theorem level_state_change_level (C R M root level : Nat) (p : Parameters)
    (initial : List PacketVector.Packet) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralLevelState C R M root p initial fields extra) :
    LiteralLevelState C R M root {p with level:=level} initial fields extra := by
  refine ⟨h.ready,h.cold,h.logWord,h.rootWord,h.windowWord,h.tagLength,?_,h.width,h.count,h.digit,
    h.bank,h.bankLength,h.bankFits,h.privateLength,h.denseCountLength,h.levelLength,h.tempLength⟩
  obtain ⟨out,priv,ho,hp,hm⟩:=h.modeWords
  refine ⟨out,priv,ho,hp,?_⟩
  intro left right i hi
  rw [WindowProvider.mode_input_change_level p M R level out priv i hi]
  exact hm left right i hi

theorem level_state_prepared (C w M root : Nat) (p : Parameters)
    (initial : List PacketVector.Packet) (left right : PacketVector.Packet)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralLevelState C (commonReserve C w) M root p initial fields extra)
    (hpC : p.C=C+9) (hrank : p.rank≤9*M) (hl : p.level≤p.rank)
    (hC : (258*M+2)^2≤C) (hw : 1≤w) (hroot : root+67≤commonReserve C w) :
    LiteralLevelState C (commonReserve C w) M root p
      (DenseAtomProgram.table C (p.level+1) (WindowProvider.modePairs p M) initial (WindowProvider.modePairs p M).length)
      (fun j=>literalLevelOutput p M C (commonReserve C w) root initial left right fields (j.natAdd 34)) extra := by
  let R:=commonReserve C w
  let fs:=levelFields R root p.level fields
  let A:=providerA C R left right fs
  let T:=WindowProvider.levelProviderOutput p M C R initial A
  have reserve : C+2≤R := LiteralCacheReuse.reserve_width C w
  have hR : 1≤R := by omega
  obtain ⟨ht,hcount,hcodes,_⟩:=WindowProvider.mode_pair_guards C M p hrank hl hC
  have hlength : (WindowProvider.modePairs p M).length=2*M := by
    simp [WindowProvider.modePairs,pairs,two_mul]
  have engine : ∀j : Fin 34,A (j.castAdd 222)=ReusableArithmetic.state C R left right j := fun j=>Fin.addCases_left j
  have tag : A 187=WindowSeed.source R (p.level+1) := by
    change fs 153=_
    simp only [fs,levelFields,Function.update_self]
    rfl
  have count : A 184=WindowSeed.source R (WindowProvider.modePairs p M).length := by
    dsimp only [A,fs]
    rw [provider_level_fields_other C R root p.level left right fields 184 (by decide) (by decide),hlength]
    exact h.count
  have ready : ProviderReady C R fs := ready_level_fields C R root p.level fields h.ready
  have master (i : Fin 256) (hi : i=151 ∨ i=152 ∨ i=177 ∨ i=178 ∨ i=179 ∨ i=183 ∨ i=184 ∨ i=185 ∨ i=187) : T i=A i :=
    WindowProvider.level_output_master p M C R initial left right A hR engine tag count (by omega) (by omega) i hi
  have original (i : Fin 256) (h152 : i≠152) (h187 : i≠187) : A i=providerA C R left right fields i :=
    provider_level_fields_other C R root p.level left right fields i h152 h187
  have mode (i : Fin 29) : T (WindowProvider.modePorts i)=ModeCacheReady.A p M R
      (ModeCacheReady.word p M) (reuseFinal 2 p M R) i :=
    WindowProvider.level_output_mode p M C R initial left right A hR engine tag count (by omega) (by omega) i
  change LiteralLevelState C R M root p _ (fun j=>T (j.natAdd 34)) extra
  refine ⟨WindowProvider.level_output_provider_ready p M C R initial left right fs hR ready tag count (by omega) (by omega),
    h.cold,h.logWord,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (master 151 (by decide)).trans ((original 151 (by decide) (by decide)).trans h.rootWord)
  · refine ⟨GradedWindow.window root p.level,?_,?_⟩
    · have bound:=GradedHalveRound.halve_iterate_le root (p.level/3)
      unfold GradedWindow.window
      omega
    · change T 152=WindowSeed.source R (GradedWindow.window root p.level)
      rw [master 152 (by decide)]
      change fs 118=_
      simp only [fs,levelFields,Function.update_of_ne (by decide : (118 : Fin 222)≠153),Function.update_self]
      rfl
  · change (T 187).length=R
    rw [master 187 (by decide),tag]
    simp only [WindowSeed.source,ZeroPadding.pad_length,CompareMachine.word,List.length_cons,List.length_replicate]
    omega
  · have guards:=ModeCacheBounded.guards C w M p hpC hrank hl hC
    refine ⟨ModeCacheReady.word p M,reuseFinal 2 p M R,guards.2.2.2.2,
      fun i=>(ModeCacheCommon.final_length 2 p M R guards.2.2.2.1 i).le,?_⟩
    intro l r i _hi
    by_cases hlarge : 34≤(WindowProvider.modePorts i).val
    · rw [provider_fields_read C R l r T _ hlarge]
      exact (mode i).symm
    · have cases : i=25 ∨ i=26 ∨ i=27 ∨ i=28 := by
        have bounds : ∀j : Fin 29,(WindowProvider.modePorts j).val<34 → j=25 ∨ j=26 ∨ j=27 ∨ j=28 := by decide
        exact bounds i (by omega)
      rcases cases with rfl|rfl|rfl|rfl <;>
        simp [ModeCacheReady.A,ModeCacheReady.caps,reuseData,Fin.addCases,providerA,
          WindowProvider.modePorts,ReusableArithmetic.state,ReusableArithmetic.bank,
          ZeroPadding.pad_zero,Rewind.Workspace.pad_zeros,Nat.max_eq_left (by omega : R+1≤R+3)]
  · exact (master 183 (by decide)).trans ((original 183 (by decide) (by decide)).trans h.width)
  · exact (master 184 (by decide)).trans ((original 184 (by decide) (by decide)).trans h.count)
  · exact (master 185 (by decide)).trans ((original 185 (by decide) (by decide)).trans h.digit)
  · exact WindowProvider.level_output_bank p M C R initial A
  · exact (DenseAtomProgram.table_length C (p.level+1) (WindowProvider.modePairs p M) initial _).trans h.bankLength
  · exact WindowProvider.level_output_table_fits p M C w initial hrank hl hC hw h.bankFits
  · intro l r i h59 h60 h62 h64 h65
    have late : ∀j : Fin 68,j≠59 → j≠60 → j≠62 → j≠64 → j≠65 → 34≤(WindowProvider.literalPorts j).val := by decide
    rw [provider_fields_read C R l r T _ (late i h59 h60 h62 h64 h65)]
    exact (WindowProvider.level_atoms_private_lengths C w (p.level+1) (WindowProvider.modePairs p M) initial
      ht hcount (fun j hj=>(hcodes j hj).le) _ i h59 h60 h62 h64 h65).le
  · change (T 129).length≤R
    dsimp only [T]
    rw [WindowProvider.level_output_count p M C R initial left right A hR engine tag count (by omega) (by omega)]
    simp only [WindowSeed.source,ZeroPadding.pad_length,CompareMachine.word,List.length_cons,List.length_replicate]
    omega
  · change (T (WindowProvider.modePorts 12)).length≤R
    rw [mode 12]
    change (ZeroPadding.pad R (List.replicate p.level true)).length≤R
    simp only [ZeroPadding.pad_length,List.length_replicate]
    omega
  · change (T 176).length≤R
    dsimp only [T]
    rw [WindowProvider.level_output_temp p M C R initial left right A hR engine tag count (by omega) (by omega),List.length_replicate]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
