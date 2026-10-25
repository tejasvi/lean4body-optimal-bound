module

public import C4Check

public section

/-! Pieces of cell `7` of the chart root grid A: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChA040

theorem k7_167 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 7) 1).2 2).2 3).2 1).2 2).2 3).1 1).2
      8926957530177883930934316429320524014278526300006388485477194921721511946696402025190174437390119557719403767525542791068058028083062579671762312509275938784836219197921970828704256187177549455358172456968905218402956990491309642146).isSome = true := by
  decide +kernel

theorem k7_168 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 7) 1).2 2).2 3).2 1).2 2).2 3).2
      6).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChA040
