module

public import C4Check

public section

/-! Pieces of cell `14` of the chart root grid C: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChC006

theorem k14_124 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 14) 1).2 1).2 2).2 3).2 1).2 2).1 3).1
      565795823501217791029674948565993483466114927807021526943494762609672701077450666112535199600870794722201095979956815392125458584876210604527026051940502108168425232429320961353938211024560340433620897262458386831283047805897381425315).isSome = true := by
  decide +kernel

theorem k14_125 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 14) 1).2 1).2 2).2 3).2 1).2 2).1 3).2
      557632093626694133399800146910356800176659575481365370498993596175400103377128784117087166324626739791772404488).isSome = true := by
  decide +kernel

theorem k14_126 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 14) 1).2 1).2 2).2 3).2 1).2 2).2 3).1
      214368948830727740703020137832802897925363746856556199087807431280011590509120943020508201472405255136225565830824).isSome = true := by
  decide +kernel

theorem k14_127 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 14) 1).2 1).2 2).2 3).2 1).2 2).2 3).2
      209631938437934832717383527664627298613000717481957978197661012451757408435441246375598731738595696379987010105288).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChC006
