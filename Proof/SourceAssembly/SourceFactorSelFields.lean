import Proof.SourceAssembly.SourceFactorSelWordsCost

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceFactorSel.FieldsGF

theorem sum_map_eq (l : List (List Bool)) :
    (l.map (fun x => 4 * x.length + 4)).sum = 4 * l.flatten.length + 4 * l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, List.length_cons, ih]
    ring

/-- One field pass's chain over all its `n` segments. -/
theorem chain_eq (n : Nat) (w : Fin n → List Bool) :
    NearCubicWires.SourceRequest.FieldPass.chainCost n w n = 4 * (List.ofFn w).flatten.length + 4 * n := by
  unfold NearCubicWires.SourceRequest.FieldPass.chainCost
  rw [List.take_of_length_le (by simp), sum_map_eq, List.length_ofFn]

/-- **The factor loop's field passes are linear in the words base.** -/
theorem fields_le (a : RepairRepresentation.DecompositionAlgorithm) {q : Nat} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (L target : Nat) (mode : Bool)
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) (MB : List Bool) (Sq : Nat)
    (hY : NearCubicWires.SourceFactorSel.WordsCost.Yb a (NearCubicWires.SourceRequest.monomialRequest L target mode atoms four, MB) ≤ Sq) :
    NearCubicWires.SourceRequest.Fields.cost (NearCubicWires.SourceRequest.header mode q L target atoms.length)
      (NearCubicWires.SourceRequest.Fields.nSlots mode atoms) (NearCubicWires.SourceRequest.Fields.sSlots mode atoms)
      (NearCubicWires.SourceRequest.Fields.tSlots a mode atoms) ≤ 1000 * (Sq + 1) := by
  have hN := NearCubicWires.SourceRequest.Fields.native_slots L target mode atoms four
  have hS := NearCubicWires.SourceRequest.Fields.support_slots a L target mode atoms four
  have hT := NearCubicWires.SourceRequest.Fields.top_slots a L target mode atoms four
  obtain ⟨_, h2, h3, _, h5, _⟩ := NearCubicWires.SourceFactorSel.WordsCost.sizes_le a
    (NearCubicWires.SourceRequest.monomialRequest L target mode atoms four)
  dsimp only [NearCubicWires.SourceFactorSel.WordsCost.Yb] at hY
  unfold NearCubicWires.SourceRequest.Fields.cost NearCubicWires.SourceRequest.FieldPass.cost
  rw [chain_eq, chain_eq, chain_eq, NearCubicWires.SourceRequest.Fields.flat5, NearCubicWires.SourceRequest.Fields.flat4,
    NearCubicWires.SourceRequest.Fields.flat4, hN, hS, hT]
  omega

end NearCubicWires.SourceFactorSel.FieldsGF
end

