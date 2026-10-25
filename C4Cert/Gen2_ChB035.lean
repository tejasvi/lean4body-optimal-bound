module

public import C4Check

public section

/-! Cells `18 ≤ n < 20` of the chart root grid B: `decide +kernel` checks that `checkBoxH2` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChB035

theorem c0 : allCells (cellOK (chModeTFM 7) chBCellBox) 18 20 [
    16185494217454273847387449190466211591129434130317780412103437990390823108314271895301802963070598359621047988047238301150587489025123701712657257535709717686963819238954533578718648502137324056583805716201904543912588016061781039883543877864896967107009306179665961,
    2] = true := by
  decide +kernel

theorem cover : Cover2 (chModeTFM 7) chBCellBox 18 20 :=
  (Cover2.cells c0)

end C4.Cert.Gen2_ChB035
