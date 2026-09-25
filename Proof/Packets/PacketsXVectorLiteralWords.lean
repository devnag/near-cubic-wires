import Proof.Packets.PacketsXVectorLiteralState

/-! A concrete cold layout. The three banks are empty; all nonconstant
input words are explicit parameters, with no machine execution premise. -/
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

def coldFields (C R M root depth : Nat) (p : Parameters) (j : Fin 222) : List Bool :=
  if j=106 then [] else
  if j=117 then ZeroPadding.pad R (List.replicate root true) else
  if j=118 then WindowSeed.source R 0 else
  if j=119 then ZeroPadding.pad R (List.replicate p.rank true) else
  if j=120 then ZeroPadding.pad R p.lower else
  if j=121 then ZeroPadding.pad R p.upper else
  if j=122 then ZeroPadding.pad R p.translation else
  if j=123 then WindowSeed.source R p.rank else
  if j=124 then ZeroPadding.pad R p.mask else
  if j=126 then ZeroPadding.pad R (List.replicate p.C true) else
  if j=143 then WindowSeed.source R depth else
  if j=149 then WindowSeed.source R (C+9) else
  if j=150 then WindowSeed.source R M else List.replicate R false

def coldExtra (R : Nat) (j : Fin 32) : List Bool :=
  if j=31 then List.replicate (R+1) false else List.replicate R false

structure ColdWordBounds (C R M root depth : Nat) (p : Parameters) : Prop where
  width : C+10 ≤ R
  population : M+1 ≤ R
  root : root ≤ R
  depth : depth+1 ≤ R
  rank : p.rank+1 ≤ R
  lower : p.lower.length ≤ R
  upper : p.upper.length ≤ R
  translation : p.translation.length ≤ R
  mask : p.mask.length ≤ R
  codeWidth : p.C ≤ R

theorem cold_fields_length (C R M root depth : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) (j : Fin 222) :
    (coldFields C R M root depth p j).length ≤ R := by
  rcases h with ⟨hwidth,hpopulation,hroot,hdepth,hrank,hlower,hupper,htranslation,hmask,hcode⟩
  by_cases h106 : j=106
  · simp only [coldFields, if_pos h106, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h117 : j=117
  · simp only [coldFields, if_neg h106, if_pos h117, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h118 : j=118
  · simp only [coldFields, if_neg h106, if_neg h117, if_pos h118, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h119 : j=119
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_pos h119, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h120 : j=120
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_pos h120, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h121 : j=121
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_pos h121, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h122 : j=122
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_neg h121, if_pos h122, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h123 : j=123
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_neg h121, if_neg h122, if_pos h123, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h124 : j=124
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_neg h121, if_neg h122, if_neg h123, if_pos h124, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h126 : j=126
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_neg h121, if_neg h122, if_neg h123, if_neg h124, if_pos h126, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h143 : j=143
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_neg h121, if_neg h122, if_neg h123, if_neg h124, if_neg h126, if_pos h143, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h149 : j=149
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_neg h121, if_neg h122, if_neg h123, if_neg h124, if_neg h126, if_neg h143, if_pos h149, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  by_cases h150 : j=150
  · simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_neg h121, if_neg h122, if_neg h123, if_neg h124, if_neg h126, if_neg h143, if_neg h149, if_pos h150, WindowSeed.source, ZeroPadding.pad_length, CompareMachine.word, List.length_replicate, List.length_cons, List.length_nil]
    omega
  simp only [coldFields, if_neg h106, if_neg h117, if_neg h118, if_neg h119, if_neg h120, if_neg h121, if_neg h122, if_neg h123, if_neg h124, if_neg h126, if_neg h143, if_neg h149, if_neg h150, List.length_replicate]
  exact le_rfl

theorem cold_provider_length (C R M root depth : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) (left right : PacketVector.Packet)
    (i : Fin 256) (hi : 34 ≤ i.val) :
    (providerA C R left right (coldFields C R M root depth p) i).length ≤ R := by
  revert hi
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · intro hi;have hj:=j.isLt;simp only [Fin.val_castAdd] at hi;omega
  · intro _
    simpa only [providerA,Fin.addCases_right] using cold_fields_length C R M root depth p h j

theorem cold_fields_ready (C R M root depth : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) :
    ProviderReady C R (coldFields C R M root depth p) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro left right i hi
    apply cold_provider_length C R M root depth p h left right i
    unfold WindowProvider.Workspace.selected at hi;omega
  · intro left right j
    apply cold_provider_length C R M root depth p h left right
    have all : ∀j,34 ≤ (WindowProvider.seedPorts (WindowSeed.privateSlot j)).val := by decide
    exact all j
  all_goals simp [coldFields]

theorem cold_fields_mode (C R M root depth : Nat) (p : Parameters)
    (left right : PacketVector.Packet) (i : Fin 29) (h12 : i≠12) (h24 : i≠24) :
    ModeCacheReady.A p M R [] (fun _=>List.replicate R false) i =
      providerA C R left right (coldFields C R M root depth p) (WindowProvider.modePorts i) := by
  have hz : ZeroPadding.pad R (List.replicate R false)=List.replicate R false := by
    simp [ZeroPadding.pad]
  have he : ZeroPadding.pad R []=List.replicate R false := by simp [ZeroPadding.pad]
  have hlog : ZeroPadding.pad (R+3) (List.replicate (R+1) false)=List.replicate (R+3) false := by
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left (by omega : R+1 ≤ R+3)]
  fin_cases i <;>
    simp_all [ModeCacheReady.A,ModeCacheReady.caps,reuseData,WindowProvider.modePorts,
      providerA,coldFields,WindowSeed.source,Fin.addCases,ReusableArithmetic.state,
      ReusableArithmetic.bank,ZeroPadding.pad_zero,hz,he,hlog]

theorem cold_words_state (C R M root depth : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) :
    LiteralColdState C R M root depth p (coldFields C R M root depth p) (coldExtra R) [] := by
  have hR : 1 ≤ R := by have hw:=h.width;omega
  refine ⟨cold_fields_ready C R M root depth p h,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    have hj31 : j≠31 := by intro he;subst j;norm_num at hj
    simp [coldExtra,hj31]
  · simp [coldExtra]
  · simp [coldFields]
  · exact ⟨0,by omega,by simp [coldFields]⟩
  · simp [coldFields]
  · refine ⟨[],(fun _=>List.replicate R false),by simp,?_,?_⟩
    · intro i;simp
    · intro left right i h12 h24
      exact cold_fields_mode C R M root depth p left right i h12 h24
  · simp [coldFields]
  · simp [coldFields]
  · simp [coldFields]
  · simp [coldFields]
  · simp [coldFields]
  · simp [coldFields]
  · intro left right i h59 h60 h62 h64 h65
    apply cold_provider_length C R M root depth p h left right
    have all : ∀j : Fin 68,j≠59 → j≠60 → j≠62 → j≠64 → j≠65 →
        34 ≤ (WindowProvider.literalPorts j).val := by decide
    exact all i h59 h60 h62 h64 h65
  · exact cold_fields_length C R M root depth p h 95
  · exact cold_fields_length C R M root depth p h 125
  · exact cold_fields_length C R M root depth p h 142

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
