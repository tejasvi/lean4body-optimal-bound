module

public import C4Check

public section

/-! Pieces of cell `2` of the chart root grid A: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChA006

theorem k2_66 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).2 1).1 2).2 2).2 3).1 3).1 1).2
      1889656158654612261856319149652408412621791566674168188972686501580458470313725498014938116629132432174538361438473).isSome = true := by
  decide +kernel

theorem k2_67 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).2 1).1 2).2 2).2 3).1 3).2
      0).isSome = true := by
  decide +kernel

theorem k2_68 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).2 1).1 2).2 2).2 3).2
      0).isSome = true := by
  decide +kernel

theorem k2_69 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chACellBox 2) 1).2 1).2
      0).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChA006
