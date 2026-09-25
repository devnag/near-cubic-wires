import Proof.Packets.PacketsXMajorityCompletePacketRun
import Proof.Packets.PhysicalRewindInto

/-! The native result is physically rewound, using the arithmetic arena's
retained width driver. Its exact list, including the zero-polynomial record,
is retained for the increasing live-assignment relabelling loop. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport NormalizedIntermediate Theorem25Completion.CycleBounds
noncomputable section

theorem normal_degree_width (C : Nat) (P : Ring.Poly Nat)
    (hn : Ring.Normal P) (hf : Fits C P) : Ring.Degree C P := by
  intro m hm
  have hd : m.Nodup := (hn.2 m hm).imp (fun h=>Nat.ne_of_lt h)
  calc
    m.length=m.toFinset.card := (List.toFinset_card_of_nodup hd).symm
    _≤(Finset.range C).card := Finset.card_le_card (by
      intro j hj
      exact Finset.mem_range.mpr (hf m hm j (List.mem_toFinset.mp hj)))
    _=C := Finset.card_range C

theorem native_reserve (C w : Nat) (P : Ring.Poly Nat)
    (hn : Ring.Normal P) (hf : Fits C P) (hc : P.length≤2^w) :
    (ExtIncidence.stream P).length≤commonReserve C w := by
  exact native_input_reserve C w P hf (normal_degree_width C P hn hf)
    (hc.trans (Nat.pow_le_pow_right (by decide) (by omega))) 30

def rewind := PhysicalRewindInto.machine (31 : Fin 45) 44
def rewound := Composition.machine machine rewind

theorem rewind_run (C R : Nat) (atoms source : List Bool) (hsource : source.length≤R) :
    Step rewind (2*R+2) (heads source) (bank C R [] [] atoms source)
      (heads []) (bank C R [] [] atoms source) := by
  have h:=PhysicalRewindInto.run R (31 : Fin 45) 44 (by decide)
    (heads source) (bank C R [] [] atoms source) (by rfl) (by rfl) hsource
  refine h.congr ?_ rfl
  funext i
  by_cases hi : i=44
  · subst i;rfl
  · rw [Function.update_of_ne hi]
    revert hi
    refine Fin.addCases (m:=34) (n:=11) (fun j _=>?_) (fun j=>?_) i
    · simp only [heads,Fin.append,Fin.addCases_left]
    refine Fin.addCases (m:=10) (n:=1) (fun k _=>?_) (fun k=>?_) j
    · simp only [heads,Fin.append,Fin.addCases_right,Fin.addCases_left]
    fin_cases k
    intro h
    exact False.elim (h rfl)

theorem rewound_run (C w d : Nat) (S : Finset Nat) (hS : ∀j∈S,j<C)
    (hw : 1≤w) (hfit : (S.card+1)^d≤2^w) (hfitAtom : S.card+1≤2^w)
    (P : Ring.Poly Nat) (hP : SubstitutionInvariant.Good C P)
    (hdeg : Ring.Degree d P) (hcount : P.length≤2^w)
    (atoms : List (Ring.Poly Nat)) (hlen : atoms.length=C) (ha : ∀Q∈atoms,Bounded S 1 Q)
    (left : Ring.Poly Nat) (hl : left.length≤2^w) :
    Step rewound (budget C (commonReserve C w) P (lowered atoms P)+1+2*commonReserve C w+2)
      (heads []) (coldBank C (commonReserve C w) left P (atomBank C (commonReserve C w) atoms) [])
      (heads []) (bank C (commonReserve C w) [] [] (atomBank C (commonReserve C w) atoms)
        (ExtIncidence.stream (Ring.norm (lowered atoms P)))) := by
  have hb:=SubstitutionCall.result_bounded d S atoms ha P hdeg
  have hn : Bounded S d (Ring.norm (lowered atoms P)) :=
    ⟨LiteralAlphabet.good_norm S _ hb.1.2,Ring.degree_norm hb.2⟩
  have hf : Fits C (Ring.norm (lowered atoms P)):=fun m hm c hc=>hS c (hn.1.2 m hm c hc)
  have hc : (Ring.norm (lowered atoms P)).length≤2^w:=(NormalizedIntermediate.census hn).trans hfit
  have first:=run C w d S hS hw hfit hfitAtom P hP hdeg hcount atoms hlen ha left hl []
  simp only [List.nil_append] at first
  have last:=rewind_run C (commonReserve C w) (atomBank C (commonReserve C w) atoms)
    (ExtIncidence.stream (Ring.norm (lowered atoms P))) (native_reserve C w _ hn.1.1 hf hc)
  simpa only [rewound,Nat.add_assoc] using first.seq last

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketRun
