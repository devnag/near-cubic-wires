import Proof.SourceAssembly.SourceRestMain

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
namespace NearCubicWires.SourceConstruction
noncomputable section

namespace Dims
variable (d : Dims)

/-- The rest layout with ten prologue residents (the five of `RestExt`, then the five driver masters). -/
structure RestExt2 (eX pX gW : Nat) : Prop where
  ext1 : d.RestExt eX pX gW
  hres2 : 19 + restPc eX pX gW + 10 ≤ d.res

/-- The dirt domain: the refill's clear set and the five refreshed tapes `B+14 .. B+18`. -/
def InDirt (eX pX gW v : Nat) : Prop := d.InClear eX pX gW v ∨ (d.B + 14 ≤ v ∧ v ≤ d.B + 18)

variable {d} {eX pX gW : Nat} (e : d.RestExt2 eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- A driver master, aligned with its target `rfT i`: `mT 0` holds `1^U0` (for `cs 2`), `mT 1..4` the templates of
`S R B v` (for `drv 0, 1, 2, 4`). -/
def mT (i : Fin 5) : Fin V :=
  ⟨d.B + 19 + restPc eX pX gW + 5 + i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres2; unfold B U G prepT; omega) hV⟩

/-- A refreshed tape: `rfT 0 = cs 2`, `rfT 1..4 = drv 0, 1, 2, 4`. -/
def rfT (i : Fin 5) : Fin V :=
  ⟨d.B + 14 + i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres2; unfold B U G prepT; omega) hV⟩

theorem mT_injective : Function.Injective (mT e hV) := fun a b h => Fin.ext (by
  have hv := congrArg Fin.val h; simp only [mT] at hv; omega)

theorem rfT_injective : Function.Injective (rfT e hV) := fun a b h => Fin.ext (by
  have hv := congrArg Fin.val h; simp only [rfT] at hv; omega)

theorem rfT_cs2 : rfT e hV 0 = csSlots e.ext1.ext hV 2 := Fin.ext rfl
theorem rfT_drv0 : rfT e hV 1 = drvSlots e.ext1.ext hV 0 := Fin.ext rfl
theorem rfT_drv1 : rfT e hV 2 = drvSlots e.ext1.ext hV 1 := Fin.ext rfl
theorem rfT_drv2 : rfT e hV 3 = drvSlots e.ext1.ext hV 2 := Fin.ext rfl
theorem rfT_drv4 : rfT e hV 4 = drvSlots e.ext1.ext hV 4 := Fin.ext rfl

end Dims

namespace Rest

theorem mT_notClear {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt2 eX pX gW) {V : Nat}
    (hV : d.U ≤ V) (i : Fin 5) : ¬ d.InClear eX pX gW (Dims.mT e hV i).val := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold SourceConstruction.Dims.InClear SourceConstruction.Dims.mT; simp only; omega

theorem mT_notOut {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt2 eX pX gW) {V : Nat}
    (hV : d.U ≤ V) (i : Fin 5) : ¬ OutV d eX pX gW (Dims.mT e hV i).val := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold OutV SourceConstruction.Dims.mT restPc; simp only; omega

end Rest
end
end NearCubicWires.SourceConstruction
end
