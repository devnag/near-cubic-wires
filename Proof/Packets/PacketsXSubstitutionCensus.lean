import Proof.Packets.PacketsXSubstitutionScanPrefix
import Proof.Packets.PacketsXNormalizedIntermediate
import Proof.Packets.PacketsXCycleArithmeticCost

/-! Semantic bounds at the actual substitution scan boundaries. All selected
indices come from bits physically read in the original monomial mask; distinct
selected codes form a subset of that monomial. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCensus
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

abbrev Bounded := NormalizedIntermediate.Bounded

theorem bounded_get (S : Finset Nat) (atoms : List (Ring.Poly Nat))
    (ha : ∀ P∈atoms,Bounded S 1 P) (j : Nat) : Bounded S 1 (atoms.getD j []) := by
  by_cases hj : j<atoms.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact ha _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact NormalizedIntermediate.zero S 1

theorem fits_of_bounded (C : Nat) (S : Finset Nat) (hS : ∀ j∈S,j<C)
    {d : Nat} {P : Ring.Poly Nat} (hP : Bounded S d P) : Fits C P := by
  intro m hm j hj
  exact hS j (hP.1.2 m hm j hj)

theorem mask_width (C : Nat) (P : Ring.Poly Nat) :
    ∀ bits∈P.map (maskNat C),bits.length=C := by
  intro bits hb
  obtain ⟨m,_,rfl⟩:=List.mem_map.mp hb
  simp [maskNat]

theorem packet_fits (C w : Nat) (P : List (List Bool))
    (hw : ∀ bits∈P,bits.length=C) (hP : P.length≤2^w) :
    PacketVector.Fits (commonReserve C w) P ∧ VectorAccumulator.Fits (commonReserve C w) P := by
  have h:=arithmetic_input_reserve C w P [] hw (by simp) hP (by simp)
  have hf : P.flatten.length≤commonReserve C w := h 25
  have hc : (CompareMachine.word P.length).length≤commonReserve C w := h 28
  refine ⟨⟨hf,hc⟩,hf,?_⟩
  simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using hc

theorem bounded_packet (C w d : Nat) (S : Finset Nat) (P : Ring.Poly Nat)
    (hP : Bounded S d P) (hfit : (S.card+1)^d≤2^w) :
    PacketVector.Fits (commonReserve C w) (P.map (maskNat C)) ∧
      VectorAccumulator.Fits (commonReserve C w) (P.map (maskNat C)) := by
  apply packet_fits C w _ (mask_width C P)
  simpa only [List.length_map] using (NormalizedIntermediate.census hP).trans hfit

theorem scan_left_property (C base : Nat) (source : List Bool) (atoms : List SubstitutionScan.Packet)
    (left right : SubstitutionScan.Packet) (property : SubstitutionScan.Packet→Prop)
    (hl : property left) (ha : ∀ j,property (atoms.getD j [])) (k : Nat) :
    property (SubstitutionScan.scan C base source atoms left right k).1 := by
  induction k with
  | zero=>exact hl
  | succ k ih=>
    simp only [SubstitutionScan.scan]
    split
    · exact ha _
    · exact ih

theorem selected_subset (C : Nat) (pre post : List Bool) (m : List Nat)
    (k : Nat) (hk : k≤C) :
    SubstitutionScan.selected C pre.length (pre++maskNat C m++post) k ⊆ m := by
  intro j hj
  obtain ⟨hr,hread⟩:=List.mem_filter.mp hj
  have hr':C-k≤j ∧ j<(C-k)+k := List.mem_range'_1.mp hr
  have hjC : j<C := by omega
  rw [SubstitutionScan.read_mask C pre post m j hjC] at hread
  exact of_decide_eq_true hread

theorem selected_length (C : Nat) (pre post : List Bool) (m : List Nat)
    (k : Nat) (hk : k≤C) :
    (SubstitutionScan.selected C pre.length (pre++maskNat C m++post) k).length≤ m.length := by
  have hn : (SubstitutionScan.selected C pre.length (pre++maskNat C m++post) k).Nodup :=
    (List.nodup_range' (s:=C-k) (n:=k)).filter _
  have hs:=selected_subset C pre post m k hk
  calc
    _=(_ : List Nat).toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _≤ m.toFinset.card := Finset.card_le_card (by intro j hj;exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hj)))
    _≤ m.length := List.toFinset_card_le m

theorem prefix_bounded (C d : Nat) (S : Finset Nat) (hS : ∀ j∈S,j<C)
    (pre post : List Bool) (m : List Nat) (hm : m.length≤d)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ P∈atoms,Bounded S 1 P)
    (left : SubstitutionScan.Packet) (k : Nat) (hk : k≤C) :
    ∃ P : Ring.Poly Nat,Bounded S d P ∧
      (SubstitutionScan.scan C pre.length (pre++maskNat C m++post)
        (atoms.map (List.map (maskNat C))) left (SubstitutionOuter.one C) k).2=P.map (maskNat C) := by
  refine ⟨NormalizedFolds.product ((SubstitutionScan.selected C pre.length
    (pre++maskNat C m++post) k).map (fun j=>atoms.getD j [])),?_,?_⟩
  · exact NormalizedIntermediate.substituted_monomial _ (bounded_get S atoms ha) _
      ((selected_length C pre post m k hk).trans hm)
  · exact SubstitutionScan.prefix_nat C pre.length (pre++maskNat C m++post) atoms
      (fun P hp=>fits_of_bounded C S hS (ha P hp)) left k hk

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCensus
