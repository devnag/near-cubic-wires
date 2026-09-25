import Proof.Packets.PacketsXVectorWorkerMetadataReady
import Proof.Packets.PacketsXVectorWorkerProjection
import Proof.Packets.PacketsXVectorWorkerState
import Proof.Packets.PacketVector

/-! Canonical boundary of the actual metadata arithmetic. Only three provider
frames and the seventeen designated numeric work tapes can change. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem metadata_canonical_run (C R u n W ci pi li : Nat) (left right acc : PacketVector.Packet)
    (previous next : List Bool) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (h180 : (fields 146).length=R) (h181 : (fields 147).length=R) (h182 : (fields 148).length=R)
    (hin : ∀j,j≠11→j≠12→j≠21→
      A C R ci pi li left right acc previous next fields extra (VectorWorkerArena.metadataSlots j)=
        DeltaScalarFields.input R u n W pi ci j)
    (hn : n<2^u) (hsum : min n W+pi<2^u) (hc : 2*ci<2^u) (hw : 2*W<2^u)
    (hR : DeltaTargetGuard.budget u+1≤R) (hN : n+2≤R)
    (hbudget : DeltaMetadata.budget u n W pi ci+1≤R) :
    ∃fields' extra',Step VectorWorkerArena.reusableMetadata (6*R+9+DeltaMetadata.budget u n W pi ci)
      (H (fun _=>0)) (A C R ci pi li left right acc previous next fields extra)
      (H (fun _=>0)) (A C R ci pi li left right acc previous next fields' extra') ∧
      fields' 146=DeltaScalarFields.fw R u (n-W) ∧
      fields' 147=DeltaScalarFields.fw R u (2*W) ∧
      fields' 148=DeltaScalarFields.fw R u (CompetitorSignedResidue.residue u u (min n W+pi) (2*ci)) ∧
      extra' 12=ZeroPadding.pad R [decide (2*ci≤ min n W+pi)] ∧
      extra' 15=ZeroPadding.pad R [decide (CompetitorSignedResidue.residue u u (min n W+pi) (2*ci)≤2*W)] ∧
      (∀j,j.val<17→(extra' j).length≤R) ∧
      (∀j,17≤j.val→extra' j=extra j) ∧
      (∀j,j≠146→j≠147→j≠148→fields' j=fields j) := by
  let base:=A C R ci pi li left right acc previous next fields extra
  obtain ⟨T,step,f180,f181,f182,f276,f279,fit,outside⟩:=VectorWorkerArena.reusable_metadata_run
    R u n W pi ci base rfl rfl h180 h181 h182 hin hn hsum hc hw hR hN hbudget
  have core : ∀i : Fin 34,T (i.castAdd 262)=ReusableArithmetic.state C R left right i := by
    intro i
    have hi:=i.isLt
    rw [outside (i.castAdd 262) (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega)
      (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega)
      (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega) (Or.inl (by simp only [Fin.val_castAdd];omega))]
    exact A_core C R ci pi li left right acc previous next fields extra i
  have saved : ∀i : Fin 8,T ((i.natAdd 256).castAdd 32)=VectorController.extraTapes R ci pi li acc previous next i := by
    intro i
    have hi:=i.isLt
    rw [outside ((i.natAdd 256).castAdd 32)
      (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega)
      (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega)
      (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega) (Or.inl (by simp only [Fin.val_castAdd,Fin.val_natAdd];omega))]
    exact A_saved C R ci pi li left right acc previous next fields extra i
  have shape:=reconstruct C R ci pi li left right acc previous next T core saved
  rw [←heads_eq] at step
  refine ⟨(fun j=>T ((j.natAdd 34).castAdd 40)),(fun j=>T (j.natAdd 264)),step.congr rfl shape,
    f180,f181,f182,f276,f279,?_,?_,?_⟩
  · intro j hj
    exact fit ⟨j.val,hj⟩
  · intro j hj
    have he:=outside (j.natAdd 264)
      (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega)
      (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega)
      (by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega) (Or.inr (by simp only [Fin.val_natAdd];omega))
    exact he.trans (A_extra C R ci pi li left right acc previous next fields extra j)
  · intro j h146 h147 h148
    have lift (k : Fin 222) (h : j≠k) : (j.natAdd 34).castAdd 40≠(k.natAdd 34).castAdd 40 := by
      intro he;apply h;apply Fin.ext;have hv:=congrArg (fun z : Fin 296=>z.val) he
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
    have he:=outside ((j.natAdd 34).castAdd 40) (lift 146 h146) (lift 147 h147) (lift 148 h148)
      (Or.inl (by have hj:=j.isLt;simp only [Fin.val_castAdd,Fin.val_natAdd];omega))
    exact he.trans (A_meta C R ci pi li left right acc previous next fields extra j)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
