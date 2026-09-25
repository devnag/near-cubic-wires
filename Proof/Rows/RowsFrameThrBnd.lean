import Proof.Rows.RowsFrameSymWords

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.FrameThrBnd
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.RepairOrdinary
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta RowsConstruction
noncomputable section

section Bnd
variable (a : DecompositionAlgorithm)

/-- **The cascade bounds of every request** (`ThrSel.bnd` on THR, `0` elsewhere). -/
def thrBnd (r : Request) (c : Fin 4) : ℕ := PacketsGlue.CursorChain.circBound a c.val r * thrFlag r

/-- The bound as a unary stage. -/
def thrBndS (c : Fin 4) : UnaryStage a (fun r => PacketsGlue.CursorChain.circBound a c.val r * thrFlag r) :=
  (PacketsConstruction.CircBound.circBoundStage a c).pairP (thrFlagStage a) mulMap2 8 2 mul_cost

/-- **On a THR request the bound IS `ThrSel.bnd`.** -/
theorem thrBnd_eq (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (c : Fin 4) : thrBnd a (.thr r four L target) c = ThrSel.bnd a r c := by
  show PacketsGlue.CursorChain.circBound a c.val (.thr r four L target) * 1 = ThrSel.bnd a r c
  rw [Nat.mul_one]
  rfl

/-- The binary word's premise, at EVERY request. -/
theorem thrBnd_lt (r : Request) (c : Fin 4) : thrBnd a r c < 2 ^ (r.input a).length := by
  have hp : 0 < 2 ^ (r.input a).length := Nat.two_pow_pos _
  cases r with
  | terminal => show _ * 0 < _; rw [Nat.mul_zero]; exact hp
  | sym r four L target => show _ * 0 < _; rw [Nat.mul_zero]; exact hp
  | thr r four L target =>
    rw [thrBnd_eq a r four L target c]
    have hT3 := ThrBounds.header_le a r four L target
    unfold ThrSel.bnd ThrSel.bndN
    split
    · have := ThrWidth.children_length_le a r four L target _ (List.get_mem r.circuits ⟨c.val, by omega⟩)
      exact lt_of_le_of_lt this Nat.lt_two_pow_self
    · exact lt_of_lt_of_le (by omega : 1 < ThrWidth.T a r four L target) (le_of_lt Nat.lt_two_pow_self)

/-- **The cascade-bound words `frame (binary |input| (thrBnd a r c))`**, one fixed machine per `c` (RX's `bndW`). -/
def thrBndW (c : Fin 4) :
    WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (thrBnd a r c))) :=
  RowsInit.BinWords.binWordS (inputLenStage a) (thrBndS a c) (fun r => thrBnd_lt a r c)

end Bnd

end
end RowsInit.FrameThrBnd
