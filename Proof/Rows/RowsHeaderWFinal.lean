import Proof.Rows.RowsHeaderWSpecOf
import Proof.Rows.RowsHeaderWMin
import Proof.Rows.RowsI2cHeader15

/-! # Rows Header writer, closed: `RowsHeaderW.hdrSpec selector a printer : RowsInit.Hdr.HdrSpec selector a printer`

**Consumer.** RX's global initializer (`FinalNE.InitHole'.initial` through `RowsInit.Hdr.HdrSpec`,
`rows-rowlevel-20260923/RowsInitHdrSpec`): the Header block of `Family.entry` on nonempty families,
`pad (PartsStep.reserveOf caps k) (RowState.commonHeader … k)` with Header 277's head at `1`.
`hdrSpec` = `hdrSpecOf` (RH, `RowsHeaderWSpecOf`) at
* Header 15: RW's `RowsConstruction.I2c.Header15.header15Stage a` (`b15_eq` by `rfl` = RH's `b15`), and
* Header 282: RH's `h282 selector a` (`RowsHeaderWMin`).
No parameter, no premise beyond the consumer's `Good` caps and `rows ≠ []`.

**Paper.** `paper.tex:1190-1212`. **Budget.** `cost_le` as `HdrSpec` demands: `c·(smallSize^d + hF + C + cC + |meta| + 1)`.
-/

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsHeaderW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-- **The rows Header writer** (RX's `HdrSpec`), closed. -/
def hdrSpec (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) :
    RowsInit.Hdr.HdrSpec selector a printer :=
  hdrSpecOf selector a printer (RowsConstruction.I2c.Header15.header15Stage a) (h282 selector a)

end
end RowsHeaderW
