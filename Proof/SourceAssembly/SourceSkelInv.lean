import Proof.SourceAssembly.SourceSkelInitRw

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

/-- **The query facts at a clause entry**: the cache's query word `wq` on `c15`, `1^C` on `c17`, `0^(C+1)` on `c18`, the query copy `q284`
of length `≤ C`, all heads `0` (`first_seam4L`'s `hq hq17 hq18 h284 hH15 hH284 hH17 hH18`, read at the entry: the init keeps them). -/
def QueryAt (c15 q284 c17 c18 : Fin T) (C : Nat) (wq : List Bool) (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop :=
  A c15 = wq ∧ A c17 = List.replicate C true ∧ A c18 = List.replicate (C+1) false ∧ (A q284).length ≤ C ∧
  H c15 = 0 ∧ H q284 = 0 ∧ H c17 = 0 ∧ H c18 = 0

/-- **Every later site entry** (the guard skips). `scr 11 = 1^Rc` with head `0`, S's clause invariant `InvC` holds at the entry at the init's
constants (`w = v = b`, `cW = cQ = cB = cS = Rc`), and every region tape is `≥ Rc` long. -/
def LaterEntry (e : d.RestExt3 eX pX gW) (Rc Rk : Nat) (Kc : Fin T → Prop) (K0 : Fin T → List Bool) (KH0 : Fin T → Nat)
    (cnt : Fin T) (b q Mb Ms S Rw B U0 : Nat) (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop :=
  A (d.scr pl.hT 11) = List.replicate Rc true ∧ H (d.scr pl.hT 11) = 0 ∧
  Rest.InvC e pl.hT Rc Rk Kc K0 KH0 cnt b q Mb Ms Rc Rc Rc Rc S Rw B b U0 H A ∧
  (∀ x : Fin T, d.F ≤ x.val → x.val < d.U → Rc ≤ (A x).length)

end
end NearCubicWires.SourceSkeleton.InitS
end

