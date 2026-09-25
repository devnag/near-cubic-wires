import Proof.SourceAssembly.SourceResidentPorts

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
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

def RestIn4 {V : Nat} (d : SourceConstruction.Dims) (eX pX gW Rc : Nat) (cur : Fin V) (K : Fin V → Prop)
    (K0 : Fin V → List Bool) (KH0 : Fin V → Nat) (m : Nat) (H : Fin V → Nat) (A : Fin V → List Bool) : Prop :=
  RestIn d eX pX gW Rc cur K K0 KH0 m H A ∧
  ∀ x : Fin V, d.InClear eX pX gW x.val → x ≠ cur → A x = List.replicate Rc false ∧ H x = 0

section facts
variable {V : Nat} {d : SourceConstruction.Dims} {eX pX gW Rc : Nat} {cur : Fin V} {K : Fin V → Prop}
  {K0 : Fin V → List Bool} {KH0 : Fin V → Nat} {m : Nat} {H : Fin V → Nat} {A : Fin V → List Bool}

/-- Every clear-set tape is at least `Rc` long. -/
theorem RestIn4.len (h : RestIn4 d eX pX gW Rc cur K K0 KH0 m H A) (x : Fin V) (hx : d.InClear eX pX gW x.val) :
    Rc ≤ (A x).length := by
  by_cases hc : x = cur
  · subst hc
    rw [h.1.2.1]
    simp only [ZeroPadding.pad, List.length_append, List.length_replicate]
    omega
  · rw [(h.2 x hx hc).1, List.length_replicate]

end facts

def srcK4 {d : SourceConstruction.Dims} {eX pX gW : Nat} {V : Nat} (cacheT : Fin 19 → Fin V) (terminal : Fin V)
    (x : Fin V) : Prop :=
  srcK3 (d := d) (eX := eX) (pX := pX) (gW := gW) cacheT x ∨ x.val = 278 ∨ x.val = 279 ∨
    x.val = d.B + 41 + restPc eX pX gW ∨
    (d.B + 43 + restPc eX pX gW ≤ x.val ∧ x.val < d.B + 51 + restPc eX pX gW) ∨ x = terminal

/-- `srcK4` meets the seams' `hKpos` once the cache and the terminal tape lie below `F`. -/
theorem srcK4_pos {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
    (cacheT : Fin 19 → Fin V) (terminal : Fin V) (hc : ∀ i, (cacheT i).val < d.F) (ht : terminal.val < d.F)
    (x : Fin V) (hx : srcK4 (d := d) (eX := eX) (pX := pX) (gW := gW) cacheT terminal x) :
    x.val < d.F ∨ (d.B + 29 + restPc eX pX gW ≤ x.val ∧ x ≠ Dims.hrT e hV 10 ∧ x ≠ Dims.hrT e hV 11) := by
  have hF := e.ext2.ext1.ext.hF
  have h10 : (Dims.hrT e hV 10).val = d.B + 29 + restPc eX pX gW + 10 := rfl
  have h11 : (Dims.hrT e hV 11).val = d.B + 29 + restPc eX pX gW + 11 := rfl
  have ne : ∀ y : Fin V, y.val ≠ d.B + 29 + restPc eX pX gW + 10 → y.val ≠ d.B + 29 + restPc eX pX gW + 11 →
      y ≠ Dims.hrT e hV 10 ∧ y ≠ Dims.hrT e hV 11 := fun y a b =>
    ⟨fun h => a (by rw [h, h10]), fun h => b (by rw [h, h11])⟩
  rcases hx with h | h | h | h | h | h
  · rcases h with h | h | ⟨i, hi⟩ | h
    · left; omega
    · left; omega
    · left; rw [← hi]; exact hc i
    · unfold SourceConstruction.Dims.HiRes at h
      right; exact ⟨h.1, ne x (by omega) (by omega)⟩
  · left; omega
  · left; omega
  · right; exact ⟨by omega, ne x (by omega) (by omega)⟩
  · right; exact ⟨by omega, ne x (by omega) (by omega)⟩
  · left; rw [h]; exact ht

end
end NearCubicWires.SourceConstruction.Rest
end
