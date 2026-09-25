import Proof.Packets.PacketsXMajorityCompletePacketLayout

/-! The actual45-tape pipeline from a resident row polynomial and normalized
atom table to its exact outer-normalized native packet. No execution premise
is used: allocation, substitution, final normalization and serialization run. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport NormalizedIntermediate
open Theorem25Completion.CycleBounds
noncomputable section

def lowered (atoms : List (Ring.Poly Nat)) (P : Ring.Poly Nat) :=
  Normalized.structuralGF2Substitute (fun code=>atoms.getD code []) P
def atomBank (C R : Nat) (atoms : List (Ring.Poly Nat)) :=
  PacketVector.bank R (SubstitutionOuter.atomMasks C atoms)
def machine := Composition.machine lower (Composition.machine normalize serialize)
def budget (C R : Nat) (P Q : Ring.Poly Nat) := SubstitutionCall.coldBudget C R P.length+1+
  (PacketOuterNormalize.budget C R Q+1+(2*((Ring.norm Q).length*(C^2+8*C+9)+8)+2*R+7))

theorem run (C w d : Nat) (S : Finset Nat) (hS : ∀j∈S,j<C)
    (hw : 1≤w) (hfit : (S.card+1)^d≤2^w) (hfitAtom : S.card+1≤2^w)
    (P : Ring.Poly Nat) (hP : SubstitutionInvariant.Good C P)
    (hdeg : Ring.Degree d P) (hcount : P.length≤2^w)
    (atoms : List (Ring.Poly Nat)) (hlen : atoms.length=C) (ha : ∀Q∈atoms,Bounded S 1 Q)
    (left : Ring.Poly Nat) (hl : left.length≤2^w) (out : List Bool) :
    Step machine (budget C (commonReserve C w) P (lowered atoms P))
      (heads out) (coldBank C (commonReserve C w) left P (atomBank C (commonReserve C w) atoms) out)
      (heads (out++ExtIncidence.stream (Ring.norm (lowered atoms P))))
      (bank C (commonReserve C w) [] [] (atomBank C (commonReserve C w) atoms)
        (out++ExtIncidence.stream (Ring.norm (lowered atoms P)))) := by
  have hb:=SubstitutionCall.result_bounded d S atoms ha P hdeg
  have hlr:=SubstitutionCall.leftResult_count w d S hfit atoms ha P hdeg left hl
  have hq : (lowered atoms P).length≤2^w:=(NormalizedIntermediate.census hb).trans hfit
  have hf : Fits C (lowered atoms P):=fun m hm c hc=>hS c (hb.1.2 m hm c hc)
  have hnorm : Bounded S d (Ring.norm (lowered atoms P)) :=
    ⟨LiteralAlphabet.good_norm S _ hb.1.2,Ring.degree_norm hb.2⟩
  have hncount : (Ring.norm (lowered atoms P)).length≤2^w:=
    (NormalizedIntermediate.census hnorm).trans hfit
  have hnfit : Fits C (Ring.norm (lowered atoms P)):=fun m hm c hc=>hS c (hnorm.1.2 m hm c hc)
  have first:=(SubstitutionCall.cold_nat_run C w d S hS hw hfit hfitAtom P hP hdeg hcount
    atoms hlen ha left hl).embed (fun _ : Fin 1=>out.length) (fun _ : Fin 1=>out)
  have first' : Step lower (SubstitutionCall.coldBudget C (commonReserve C w) P.length)
      (heads out) (coldBank C (commonReserve C w) left P (atomBank C (commonReserve C w) atoms) out)
      (heads out) (bank C (commonReserve C w) (SubstitutionCall.leftResult atoms P left)
        (lowered atoms P) (atomBank C (commonReserve C w) atoms) out) :=
    (first.congr_in (heads_embed out) rfl).congr (heads_embed out) (bank_embed _ _ _ _ _ _)
  exact first'.seq ((normalize_run C w (SubstitutionCall.leftResult atoms P left)
    (lowered atoms P) _ out hw hb.1.1 hf hlr hq).seq
    (serialize_run C w (Ring.norm (lowered atoms P)) _ out hnfit hnorm.1.1 hncount))


end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketRun
