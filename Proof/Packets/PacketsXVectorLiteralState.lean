import Proof.Packets.PacketsXVectorLiteralBootLayout

/-! Data obligations before the physical controller boot; no execution premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
noncomputable section
structure LiteralColdState (C R M root depth : Nat) (p : Parameters)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (initialBank : List Bool := PacketVector.bank R (List.replicate C [])) : Prop where
  ready : ProviderReady C R fields
  cold : ∀j,j.val<31 → extra j=List.replicate R false
  logWord : extra 31=List.replicate (R+1) false
  rootWord : fields 117=ZeroPadding.pad R (List.replicate root true)
  windowWord : ∃old,old+1≤R ∧ fields 118=WindowSeed.source R old
  tagLength : (fields 153).length=R
  modeWords : ∃out priv,out.length≤R ∧ (∀i,(priv i).length≤R) ∧
    ∀left right i,i≠12 → i≠24 →
      ModeCacheReady.A p M R out priv i=providerA C R left right fields (WindowProvider.modePorts i)
  width : fields 149=WindowSeed.source R (C+9)
  sourcePopulation : fields 150=WindowSeed.source R M
  sourceDepth : fields 143=WindowSeed.source R depth
  blankMode : fields 127=List.replicate R false
  blankDigit : fields 151=List.replicate R false
  bank : fields 106=initialBank
  privateLength : ∀left right i,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 →
    (providerA C R left right fields (WindowProvider.literalPorts i)).length≤R
  denseCountLength : (fields 95).length≤R
  levelLength : (fields 125).length≤R
  tempLength : (fields 142).length≤R

theorem boot_provider_other (C R M : Nat) (left right : PacketVector.Packet)
    (fields : Fin 222 → List Bool) (i : Fin 256) (h161 : i≠161) (h184 : i≠184) (h185 : i≠185) :
    providerA C R left right (bootFields R M fields) i=providerA C R left right fields i := by
  revert h161 h184 h185
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · intros;simp only [providerA,Fin.addCases_left]
  · intro h161 h184 h185
    have h127 : j≠127 := by intro he;subst j;exact h161 rfl
    have h150 : j≠150 := by intro he;subst j;exact h184 rfl
    have h151 : j≠151 := by intro he;subst j;exact h185 rfl
    simp only [providerA,Fin.addCases_right,bootFields,Function.update_of_ne h127,
      Function.update_of_ne h150,Function.update_of_ne h151]

theorem boot_provider_ready (C R M : Nat) (fields : Fin 222 → List Bool) (h : ProviderReady C R fields) :
    ProviderReady C R (bootFields R M fields) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro left right i hi
    have small : i.val<150 := by unfold WindowProvider.Workspace.selected at hi;omega
    rw [boot_provider_other C R M left right fields i]
    · exact h.work left right i hi
    all_goals intro he;subst i;norm_num at small
  · intro left right j
    have small : (WindowProvider.seedPorts (WindowSeed.privateSlot j)).val<96 := by
      have all : ∀j,(WindowProvider.seedPorts (WindowSeed.privateSlot j)).val<96 := by decide
      exact all j
    rw [boot_provider_other C R M left right fields _]
    · exact h.seedWords left right j
    all_goals intro he;rw [he] at small;norm_num at small
  · simpa [bootFields,Function.update] using h.frame180
  · simpa [bootFields,Function.update] using h.frame181
  · simpa [bootFields,Function.update] using h.frame182

theorem cold_state_boot (C R M root depth : Nat) (p : Parameters)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralColdState C R M root depth p fields extra) (hR : 1≤R) :
    LiteralLevelState C R M root p (List.replicate C []) (bootFields R M fields) (bootExtra R M extra) := by
  refine ⟨boot_provider_ready C R M fields h.ready,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    have hn : j≠17 := by intro he;subst j;norm_num at hj
    simp only [bootExtra,Function.update_of_ne hn]
    exact h.cold j (by omega)
  · simpa [bootExtra,Function.update] using h.logWord
  · simpa [bootFields,Function.update] using h.rootWord
  · simpa [bootFields,Function.update] using h.windowWord
  · simpa [bootFields,Function.update] using h.tagLength
  · obtain ⟨out,priv,ho,hp,hm⟩:=h.modeWords
    refine ⟨out,priv,ho,hp,?_⟩
    intro left right i hi
    by_cases he : i=24
    · subst i
      simp [ModeCacheReady.A,ModeCacheReady.caps,reuseData,WindowProvider.modePorts,
        providerA,bootFields,Function.update,WindowSeed.source,Fin.addCases]
    · rw [boot_provider_other C R M left right fields _]
      · exact hm left right i hi he
      · have all : ∀j : Fin 29,j≠24 → WindowProvider.modePorts j≠161 := by decide
        exact all i he
      all_goals have all : ∀j : Fin 29,WindowProvider.modePorts j≠184 ∧ WindowProvider.modePorts j≠185 := by decide
      · exact (all i).1
      · exact (all i).2
  · simpa [bootFields,Function.update] using h.width
  · simp [bootFields,Function.update]
  · simp [bootFields,Function.update]
  · simpa [bootFields,Function.update] using h.bank
  · simp
  · intro P hP
    have hp : P=[] := (List.mem_replicate.mp hP).2
    subst P;exact PacketVector.empty_fits R hR
  · intro left right i h59 h60 h62 h64 h65
    have large : 186 ≤ (WindowProvider.literalPorts i).val := by
      have all : ∀j : Fin 68,j≠59 → j≠60 → j≠62 → j≠64 → j≠65 → 186 ≤ (WindowProvider.literalPorts j).val := by decide
      exact all i h59 h60 h62 h64 h65
    rw [boot_provider_other C R M left right fields _]
    · exact h.privateLength left right i h59 h60 h62 h64 h65
    all_goals intro he;rw [he] at large;norm_num at large
  · simpa [bootFields,Function.update] using h.denseCountLength
  · simpa [bootFields,Function.update] using h.levelLength
  · simpa [bootFields,Function.update] using h.tempLength

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
