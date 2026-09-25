import Proof.Packets.PacketsXVectorWorkerMetadataCanonical
import Proof.Packets.PacketsXVectorWorkerValidity
import Proof.Packets.PacketsXVectorWorkerEffects
import Proof.Packets.PacketsXVectorWorkerProviderDock

/-! One actual delta call: overwrite the scalar frames, inspect the two
physical validity bits, run the finite literal-window provider when valid,
and erase all numeric scratch before the next child. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def deltaPacket (n W parent child : Nat) (window : Nat→PacketVector.Packet) : PacketVector.Packet:=
  match SupplierListPolynomial.deltaTarget? n W parent child with
  | none=>[]
  | some target=>window target

attribute [local irreducible] VectorWorkerArena.reusableMetadata VectorWorkerArena.erase
attribute [local irreducible] VectorWorkerArena.deltaBranch delta

theorem delta_round_run {s : Nat} (p : Machine 256 s) (C R u n W ci pi li K : Nat)
    (left right acc : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (window : Nat→PacketVector.Packet)
    (Q : (Fin 222→List Bool)→Prop)
    (hr : VectorAccumulator.Fits R right) (hpositive : 1≤R)
    (h180 : (fields 146).length=R) (h181 : (fields 147).length=R) (h182 : (fields 148).length=R)
    (hcold : ∀j,j.val<17→extra j=List.replicate R false)
    (hin : ∀j,j≠11→j≠12→j≠21→
      A C R ci pi li left right acc previous next fields extra (VectorWorkerArena.metadataSlots j)=
        DeltaScalarFields.input R u n W pi ci j)
    (hn : n<2^u) (hsum : min n W+pi<2^u) (hc : 2*ci<2^u) (hw : 2*W<2^u)
    (hR : DeltaTargetGuard.budget u+1≤R) (hN : n+2≤R)
    (hbudget : DeltaMetadata.budget u n W pi ci+1≤R)
    (invalid_ready : ∀f,
      f 146=DeltaScalarFields.fw R u (n-W)→f 147=DeltaScalarFields.fw R u (2*W)→
      f 148=DeltaScalarFields.fw R u (CompetitorSignedResidue.residue u u (min n W+pi) (2*ci))→
      (∀j,j≠146→j≠147→j≠148→f j=fields j)→Q f)
    (provider_run : ∀target f,SupplierListPolynomial.deltaTarget? n W pi ci=some target→
      f 146=DeltaScalarFields.fw R u (n-W)→f 147=DeltaScalarFields.fw R u (2*W)→
      f 148=DeltaScalarFields.fw R u target→
      (∀j,j≠146→j≠147→j≠148→f j=fields j)→
      ∃out,Step p K providerH (providerA C R left [] f) providerH (providerA C R left (window target) out) ∧Q out) :
    ∃out,Step (delta p) (12*R+DeltaMetadata.budget u n W pi ci+K+27)
      (H (fun _=>0)) (A C R ci pi li left right acc previous next fields extra)
      (H (fun _=>0)) (A C R ci pi li left (deltaPacket n W pi ci window) acc previous next out extra) ∧Q out := by
  obtain ⟨f,e,first,f180,f181,f182,e276,e279,fit,retained,fieldRetained⟩:=
    metadata_canonical_run C R u n W ci pi li left right acc previous next fields extra
      h180 h181 h182 hin hn hsum hc hw hR hN hbudget
  have restore : clearedExtra R e=extra := by
    funext j
    by_cases hj:j.val<17
    · simp only [clearedExtra,if_pos hj,hcold j hj]
    · simp only [clearedExtra,if_neg hj,retained j (by omega)]
  have finish (answer : PacketVector.Packet) (out : Fin 222→List Bool)
      (middle : Step (VectorWorkerArena.deltaBranch (RecoveryFocus.machine providerSlots p))
        (4*R+K+12) (H (fun _=>0)) (A C R ci pi li left right acc previous next f e)
        (H (fun _=>0)) (A C R ci pi li left answer acc previous next out e)) :
      Step (delta p) (12*R+DeltaMetadata.budget u n W pi ci+K+27)
        (H (fun _=>0)) (A C R ci pi li left right acc previous next fields extra)
        (H (fun _=>0)) (A C R ci pi li left answer acc previous next out extra) := by
    have last:=VectorWorkerArena.erase_run R (A C R ci pi li left answer acc previous next out e)
      (by
        intro j
        rw [show VectorWorkerArena.scratch j=(j.castAdd 15).natAdd 264 from Fin.ext rfl,A_extra]
        exact fit (j.castAdd 15) j.isLt) rfl rfl
    rw [←heads_eq] at last
    have endEq:VectorWorkerArena.cleared R (A C R ci pi li left answer acc previous next out e)=
        A C R ci pi li left answer acc previous next out extra := by
      rw [cleared_canonical,restore]
    have joined:=first.seq (middle.seq (last.congr rfl endEq))
    have fuel : (6*R+9+DeltaMetadata.budget u n W pi ci)+1+((4*R+K+12)+1+(2*R+4))=
        12*R+DeltaMetadata.budget u n W pi ci+K+27 := by omega
    rw [fuel] at joined
    simpa only [delta] using joined
  cases ht:SupplierListPolynomial.deltaTarget? n W pi ci with
  | none=>
    have middle:=VectorWorkerArena.branch_none (RecoveryFocus.machine providerSlots p) R u n W pi ci
      (A C R ci pi li left right acc previous next f e) rfl rfl
      (VectorAccumulator.flat_length R right hr) (VectorAccumulator.count_length R right hr)
      hsum e276 e279 ht
    rw [←heads_eq] at middle
    have endEq:=right_zero_canonical C R ci pi li left right acc previous next f e hpositive
    have result:=finish [] f ((middle.congr rfl endEq).enlarge (by omega))
    refine ⟨f,?_,invalid_ready f f180 f181 f182 fieldRetained⟩
    simpa only [deltaPacket,ht] using result
  | some target=>
    have flags:=VectorWorkerArena.flags_of_some R u n W pi ci target
      (A C R ci pi li left right acc previous next f e) hsum e276 e279 ht
    obtain ⟨out,small,hq⟩:=provider_run target f ht f180 f181 (by simpa only [flags.2.2] using f182) fieldRetained
    have provider:=provider_dock C R ci pi li left [] left (window target) acc previous next f e
      (providerA C R left (window target) out) small (fun j=>Fin.addCases_left j)
    have fieldEq : (fun j=>providerA C R left (window target) out (j.natAdd 34))=out := by
      funext j;exact Fin.addCases_right j
    rw [fieldEq] at provider
    have startEq:=right_zero_canonical C R ci pi li left right acc previous next f e hpositive
    have middle:=VectorWorkerArena.branch_valid R (A C R ci pi li left right acc previous next f e)
      (A C R ci pi li left (window target) acc previous next out e) rfl rfl
      (VectorAccumulator.flat_length R right hr) (VectorAccumulator.count_length R right hr)
      flags.1 flags.2.1 (by rw [startEq,←heads_eq];exact provider)
    rw [←heads_eq] at middle
    refine ⟨out,?_,hq⟩
    simpa only [deltaPacket,ht] using finish (window target) out middle

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
