import Proof.Packets.PacketsXVectorLiteralLevelTransaction

/-! Data-only entry invariant for repeated concrete level updates. It records
actual resident words and packet capacities, not execution assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache Theorem25Completion.CycleBounds
noncomputable section

structure LiteralLevelState (C R M root : Nat) (p : Parameters)
    (initial : List PacketVector.Packet) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool) : Prop where
  ready : ProviderReady C R fields
  cold : ∀j,j.val<17 → extra j=List.replicate R false
  logWord : extra 31=List.replicate (R+1) false
  rootWord : fields 117=ZeroPadding.pad R (List.replicate root true)
  windowWord : ∃old,old+1≤R ∧ fields 118=WindowSeed.source R old
  tagLength : (fields 153).length=R
  modeWords : ∃out priv,out.length≤R ∧ (∀i,(priv i).length≤R) ∧
    ∀left right i,i≠12 → ModeCacheReady.A p M R out priv i=providerA C R left right fields (WindowProvider.modePorts i)
  width : fields 149=WindowSeed.source R (C+9)
  count : fields 150=WindowSeed.source R (2*M)
  digit : fields 151=WindowSeed.source R (Nat.log 2 (2*M)+1)
  bank : fields 106=PacketVector.bank R initial
  bankLength : initial.length=C
  bankFits : ∀P∈initial,PacketVector.Fits R P
  privateLength : ∀left right i,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 →
    (providerA C R left right fields (WindowProvider.literalPorts i)).length≤R
  denseCountLength : (fields 95).length≤R
  levelLength : (fields 125).length≤R
  tempLength : (fields 142).length≤R

theorem level_state_window (C R M root ci pi level : Nat) (p : Parameters)
    (initial : List PacketVector.Packet) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralLevelState C R M root p initial fields extra) (hR : 1≤R)
    (left right : PacketVector.Packet) (previous next : List Bool) :
    ∃old,old+1≤R ∧ ∀j,A C R ci pi level left right [] previous next fields extra (VectorWorkerArena.windowSlots j)=
      GradedWindow.A R root level 0 0 old j := by
  obtain ⟨old,ho,hw⟩:=h.windowWord
  refine ⟨old,ho,?_⟩
  intro j
  fin_cases j
  · change extra 0=ZeroPadding.pad R (List.replicate 0 true)
    simpa [ZeroPadding.pad] using h.cold 0 (by decide)
  · exact h.cold 2 (by decide)
  · exact h.cold 3 (by decide)
  · exact h.cold 4 (by decide)
  · exact h.logWord
  · rfl
  · rfl
  · change extra 5=ZeroPadding.pad R (CompareMachine.word 0)
    rw [GradedWindow.zero_count R hR]
    exact h.cold 5 (by decide)
  · exact h.cold 6 (by decide)
  · exact hw
  · exact h.cold 7 (by decide)
  · exact h.rootWord
  · rfl

theorem provider_retained_equal (C R : Nat) (left right : PacketVector.Packet)
    (fields fields' : Fin 222 → List Bool)
    (he : ∀j,ProviderRetained j → j≠146 → j≠147 → j≠148 → fields' j=fields j)
    (i : Fin 256) (hi : i.val<34 ∨ i=125 ∨ i=129 ∨ i=140 ∨ 150 ≤ i.val)
    (h180 : i≠180) (h181 : i≠181) (h182 : i≠182) :
    providerA C R left right fields' i=providerA C R left right fields i := by
  revert hi h180 h181 h182
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · intros;simp only [providerA,Fin.addCases_left]
  · intro hi h180 h181 h182
    simp only [providerA,Fin.addCases_right]
    apply he j
    · unfold ProviderRetained
      norm_num [Fin.ext_iff] at hi ⊢
      omega
    all_goals intro hj;subst j;contradiction

theorem level_state_preserved (C R M root : Nat) (p : Parameters)
    (initial : List PacketVector.Packet) (fields fields' : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralLevelState C R M root p initial fields extra)
    (hr : ProviderReady C R fields')
    (he : ∀j,ProviderRetained j → j≠146 → j≠147 → j≠148 → fields' j=fields j) :
    LiteralLevelState C R M root p initial fields' extra := by
  have point (j : Fin 222) (hj : j=95 ∨ j=106 ∨ j=117 ∨ j=118 ∨ j=125 ∨ j=142 ∨
      j=149 ∨ j=150 ∨ j=151 ∨ j=153) : fields' j=fields j := by
    apply he j
    · unfold ProviderRetained;rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    all_goals rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  refine ⟨hr,h.cold,h.logWord,?_,?_,?_,?_,?_,?_,?_,?_,h.bankLength,h.bankFits,?_,?_,?_,?_⟩
  · exact (point 117 (by decide)).trans h.rootWord
  · obtain ⟨old,ho,hw⟩:=h.windowWord
    exact ⟨old,ho,(point 118 (by decide)).trans hw⟩
  · rw [point 153 (by decide)];exact h.tagLength
  · obtain ⟨out,priv,ho,hp,hm⟩:=h.modeWords
    refine ⟨out,priv,ho,hp,?_⟩
    intro left right i hi
    rw [provider_retained_equal C R left right fields fields' he _]
    · exact hm left right i hi
    all_goals have away : ∀j,(WindowProvider.modePorts j).val<34 ∨ WindowProvider.modePorts j=125 ∨
        WindowProvider.modePorts j=129 ∨ WindowProvider.modePorts j=140 ∨ 150 ≤ (WindowProvider.modePorts j).val := by decide
    · exact away i
    all_goals have away' : ∀j,WindowProvider.modePorts j≠180 ∧ WindowProvider.modePorts j≠181 ∧ WindowProvider.modePorts j≠182 := by decide
    · exact (away' i).1
    · exact (away' i).2.1
    · exact (away' i).2.2
  · exact (point 149 (by decide)).trans h.width
  · exact (point 150 (by decide)).trans h.count
  · exact (point 151 (by decide)).trans h.digit
  · exact (point 106 (by decide)).trans h.bank
  · intro left right i h59 h60 h62 h64 h65
    have late : ∀j : Fin 68,j≠59 → j≠60 → j≠62 → j≠64 → j≠65 → 186 ≤ (WindowProvider.literalPorts j).val := by decide
    have hl:=late i h59 h60 h62 h64 h65
    rw [provider_retained_equal C R left right fields fields' he _ (by omega)
      (by intro he;rw [he] at hl;norm_num at hl) (by intro he;rw [he] at hl;norm_num at hl)
      (by intro he;rw [he] at hl;norm_num at hl)]
    exact h.privateLength left right i h59 h60 h62 h64 h65
  · rw [point 95 (by decide)];exact h.denseCountLength
  · rw [point 125 (by decide)];exact h.levelLength
  · rw [point 142 (by decide)];exact h.tempLength

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
