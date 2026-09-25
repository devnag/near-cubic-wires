import Proof.SourceAssembly.SourceFirstSeam3A

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- **`InvR` moves from the counter universe to the source universe** (the first code runs on `V+1` tapes, the loop on `V`):
the layout's tapes are the same values, so every field transports along `Fin.castSucc`. -/
theorem InvR.restrict {d : SourceConstruction.Dims} {eX pX gW : Nat} {e : d.RestExt3 eX pX gW} {V : Nat}
    {hV : d.U ≤ V} {hV1 : d.U ≤ V + 1}
    {Rc Rk : Nat} {K1 : Fin (V+1) → Prop} {K01 : Fin (V+1) → List Bool} {KH01 : Fin (V+1) → Nat}
    {j w q Mb Ms cW cQ cB cS S Rw B v U0 fuel : Nat} {H : Fin (V+1) → Nat} {A : Fin (V+1) → List Bool}
    (h : InvR e hV1 Rc Rk K1 K01 KH01 j w q Mb Ms cW cQ cB cS S Rw B v U0 fuel H A)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hK : ∀ y, K y → K1 y.castSucc) (hK0 : ∀ y, K y → K01 y.castSucc = K0 y ∧ KH01 y.castSucc = KH0 y) :
    InvR e hV Rc Rk K K0 KH0 j w q Mb Ms cW cQ cB cS S Rw B v U0 fuel (fun y => H y.castSucc) (fun y => A y.castSucc) := by
  have crs : ∀ i : Fin 5, (d.rsT e.ext2.ext1 hV i).castSucc = d.rsT e.ext2.ext1 hV1 i := fun _ => Fin.ext rfl
  have cmT : ∀ i : Fin 5, (Dims.mT e.ext2 hV i).castSucc = Dims.mT e.ext2 hV1 i := fun _ => Fin.ext rfl
  have csc : ∀ m : Fin 13, (d.scr hV m).castSucc = d.scr hV1 m := fun _ => Fin.ext rfl
  have chr : ∀ i : Fin 12, (Dims.hrT e hV i).castSucc = Dims.hrT e hV1 i := fun _ => Fin.ext rfl
  have cen : ∀ kk : Fin 13, (Dims.encT (d := d) hV kk).castSucc = Dims.encT (d := d) hV1 kk := fun _ => Fin.ext rfl
  refine ⟨fun y hy => ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x hx hz => h.dirtA x.castSucc hx hz, fun x hx hz => h.dirtH x.castSucc hx hz,
    fun x h1 h2 => h.famH x.castSucc h1 h2, fun x hz => h.zA x.castSucc hz, fun x hz => h.zH x.castSucc hz,
    fun kk hk => ?_⟩
  · have := h.kept y.castSucc (hK y hy)
    rw [(hK0 y hy).1, (hK0 y hy).2] at this; exact this
  · show A (d.rsT e.ext2.ext1 hV 2).castSucc = _; rw [crs]; exact h.curT
  · show A (d.rsT e.ext2.ext1 hV 0).castSucc = _; rw [crs]; exact h.big
  · show A (d.rsT e.ext2.ext1 hV 1).castSucc = _; rw [crs]; exact h.small
  · show A (d.rsT e.ext2.ext1 hV 3).castSucc = _; rw [crs]; exact h.wv
  · show A (d.rsT e.ext2.ext1 hV 4).castSucc = _; rw [crs]; exact h.qv
  · show H (d.rsT e.ext2.ext1 hV i).castSucc = _; rw [crs]; exact h.rsH i
  · show A (Dims.mT e.ext2 hV 0).castSucc = _; rw [cmT]; exact h.mU
  · show A (Dims.mT e.ext2 hV 1).castSucc = _; rw [cmT]; exact h.mS
  · show A (Dims.mT e.ext2 hV 2).castSucc = _; rw [cmT]; exact h.mR
  · show A (Dims.mT e.ext2 hV 3).castSucc = _; rw [cmT]; exact h.mB
  · show A (Dims.mT e.ext2 hV 4).castSucc = _; rw [cmT]; exact h.mv
  · show H (Dims.mT e.ext2 hV i).castSucc = _; rw [cmT]; exact h.mH i
  · show A (d.scr hV 11).castSucc = _; rw [csc]; exact h.drv
  · show H (d.scr hV 11).castSucc = _; rw [csc]; exact h.drvH
  · show A (d.scr hV 12).castSucc = _; rw [csc]; exact h.lg
  · show H (d.scr hV 12).castSucc = _; rw [csc]; exact h.lgH
  · show A (Dims.hrT e hV 10).castSucc = _; rw [chr]; exact h.zD
  · show H (Dims.hrT e hV 10).castSucc = _; rw [chr]; exact h.zDH
  · show A (Dims.hrT e hV 11).castSucc = _; rw [chr]; exact h.zL
  · show H (Dims.hrT e hV 11).castSucc = _; rw [chr]; exact h.zLH
  · show H (Dims.encT (d := d) hV kk).castSucc = _; rw [cen]; exact h.encH kk hk

theorem backCost_eq {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (rq : Request) (Rc w q L Mb Ms : Nat) :
    backCost se sp rq Rc w q L Mb Ms = 14 * Rc + backCost se sp rq 0 w q L Mb Ms := by
  simp only [backCost, Prologue.f6FullCost, Prologue.f6Cost]
  omega

theorem first_windows_of_free {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (g70 : Nat) (rq : Request) (Rc w q L Mb Ms c0 : Nat)
    (h : g70 + 1 + backCost se sp rq 0 w q L Mb Ms + c0 + 2 ≤ Rc) :
    g70 + 1 + c0 + 1 ≤ Rc ∧ (g70 + 1 + backCost se sp rq Rc w q L Mb Ms) + 1 + c0 + 1 ≤ 16 * (Rc + 1) := by
  rw [backCost_eq se sp rq Rc]
  constructor <;> omega

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end
