import Proof.SourceAssembly.SourceSkelInv

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

section transfer
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- **`InvC` survives a bank change that keeps the site region** and resets the kept tapes to new kept values. -/
theorem InvC.transfer {Rc Rk : Nat} {Kc : Fin V → Prop} {K0 K0' : Fin V → List Bool} {KH0 : Fin V → Nat} {cnt : Fin V}
    {w q Mb Ms cW cQ cB cS S Rw B v U0 : Nat} {H H' : Fin V → Nat} {A A' : Fin V → List Bool}
    (h : InvC e hV Rc Rk Kc K0 KH0 cnt w q Mb Ms cW cQ cB cS S Rw B v U0 H A)
    (hcnt : d.F ≤ cnt.val)
    (hF : ∀ x : Fin V, d.F ≤ x.val → A' x = A x ∧ H' x = H x)
    (hK : ∀ x, Kc x → A' x = K0' x ∧ H' x = KH0 x) :
    InvC e hV Rc Rk Kc K0' KH0 cnt w q Mb Ms cW cQ cB cS S Rw B v U0 H' A' := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have vrs : ∀ i : Fin 5, (d.rsT e.ext2.ext1 hV i).val = d.B + 19 + restPc eX pX gW + i.val := fun _ => rfl
  have vmT : ∀ i : Fin 5, (Dims.mT e.ext2 hV i).val = d.B + 19 + restPc eX pX gW + 5 + i.val := fun _ => rfl
  have vscr : ∀ m : Fin 13, (d.scr hV m).val = d.G + d.R1 + 397 + d.w + d.tc + m.val := fun _ => rfl
  have vhr : ∀ i : Fin 12, (Dims.hrT e hV i).val = d.B + 29 + restPc eX pX gW + i.val := fun _ => rfl
  have venc : ∀ kk : Fin 13, (Dims.encT (d := d) hV kk).val = d.F + d.rt + kk.val := fun _ => rfl
  have hDirt : ∀ x : Fin V, d.InDirt eX pX gW x.val → d.F ≤ x.val := by
    intro x hx
    unfold SourceConstruction.Dims.InDirt SourceConstruction.Dims.InClear at hx
    omega
  have hZ : ∀ x : Fin V, d.InZ eX pX x.val → d.F ≤ x.val := by
    intro x hx
    unfold SourceConstruction.Dims.InZ at hx
    omega
  have rsF : ∀ i : Fin 5, d.F ≤ (d.rsT e.ext2.ext1 hV i).val := fun i => by rw [vrs]; omega
  have mF : ∀ i : Fin 5, d.F ≤ (Dims.mT e.ext2 hV i).val := fun i => by rw [vmT]; omega
  have sF : ∀ m : Fin 13, d.F ≤ (d.scr hV m).val := fun m => by rw [vscr]; omega
  have hF10 : d.F ≤ (Dims.hrT e hV 10).val := by rw [vhr]; omega
  have hF11 : d.F ≤ (Dims.hrT e hV 11).val := by rw [vhr]; omega
  have eF : ∀ kk : Fin 13, d.F ≤ (Dims.encT (d := d) hV kk).val := fun kk => by rw [venc]; omega
  refine ⟨hK, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x hx hz => ?_, fun x hx hz => ?_, fun x hz => ?_, fun x hz => ?_, ?_, ?_, ?_, ?_, fun kk hk => ?_, fun kk hk => ?_⟩
  · rw [(hF _ (rsF 0)).1]; exact h.big
  · rw [(hF _ (rsF 1)).1]; exact h.small
  · rw [(hF _ (rsF 3)).1]; exact h.wv
  · rw [(hF _ (rsF 4)).1]; exact h.qv
  · rw [(hF _ (rsF i)).2]; exact h.rsH i hi
  · rw [(hF _ (mF 0)).1]; exact h.mU
  · rw [(hF _ (mF 1)).1]; exact h.mS
  · rw [(hF _ (mF 2)).1]; exact h.mR
  · rw [(hF _ (mF 3)).1]; exact h.mB
  · rw [(hF _ (mF 4)).1]; exact h.mv
  · rw [(hF _ (mF i)).2]; exact h.mH i
  · rw [(hF _ (sF 11)).1]; exact h.drv
  · rw [(hF _ (sF 11)).2]; exact h.drvH
  · rw [(hF _ (sF 12)).1]; exact h.lg
  · rw [(hF _ (sF 12)).2]; exact h.lgH
  · rw [(hF _ hF10).1]; exact h.zD
  · rw [(hF _ hF10).2]; exact h.zDH
  · rw [(hF _ hF11).1]; exact h.zL
  · rw [(hF _ hF11).2]; exact h.zLH
  · rw [(hF x (hDirt x hx)).1]; exact h.dirtA x hx hz
  · rw [(hF x (hDirt x hx)).2]; exact h.dirtH x hx hz
  · rw [(hF x (hZ x hz)).1]; exact h.zA x hz
  · rw [(hF x (hZ x hz)).2]; exact h.zH x hz
  · rw [(hF _ (rsF 2)).1]; exact h.curA
  · rw [(hF _ (rsF 2)).2]; exact h.curH
  · rw [(hF _ hcnt).1]; exact h.cntA
  · rw [(hF _ hcnt).2]; exact h.cntH
  · rw [(hF _ (eF kk)).1]; exact h.encA kk hk
  · rw [(hF _ (eF kk)).2]; exact h.encH kk hk

end transfer
end
end NearCubicWires.SourceConstruction.Rest

namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section
open NearCubicWires.SourceConstruction.Rest

variable {d : Dims} {eX pX gW eR eV X T : Nat} {pl : Place d eX pX gW eR eV X T}

theorem laterEntry_transfer {e : d.RestExt3 eX pX gW} {Rc Rk : Nat} {Kc : Fin T → Prop} {K0 K0' : Fin T → List Bool}
    {KH0 : Fin T → Nat} {cnt : Fin T} {b q Mb Ms S Rw B U0 : Nat} {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (h : LaterEntry pl e Rc Rk Kc K0 KH0 cnt b q Mb Ms S Rw B U0 H A)
    (hcnt : d.F ≤ cnt.val)
    (hF : ∀ x : Fin T, d.F ≤ x.val → A' x = A x ∧ H' x = H x)
    (hK : ∀ x, Kc x → A' x = K0' x ∧ H' x = KH0 x) :
    LaterEntry pl e Rc Rk Kc K0' KH0 cnt b q Mb Ms S Rw B U0 H' A' := by
  have hG : d.G = d.F + d.rt + 13 := rfl
  have vscr : ∀ m : Fin 13, (d.scr pl.hT m).val = d.G + d.R1 + 397 + d.w + d.tc + m.val := fun _ => rfl
  have s11 : d.F ≤ (d.scr pl.hT 11).val := by rw [vscr]; omega
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [(hF _ s11).1]; exact h1, by rw [(hF _ s11).2]; exact h2, InvC.transfer e pl.hT h3 hcnt hF hK,
    fun x hx1 hx2 => ?_⟩
  rw [(hF x hx1).1]
  exact h4 x hx1 hx2

end
end NearCubicWires.SourceSkeleton.InitS
end
