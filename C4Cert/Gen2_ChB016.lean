module

public import C4Check

public section

/-! Pieces of cell `15` of the chart root grid B: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChB016

theorem k15_210 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).2 2).2 3).2 1).2 2).2 3).2 1).2 2).1 3).2 2).2
      57335665245405884023512888710625921750467403994762647980557166380488665716685834783771942579841810057395535380196440).isSome = true := by
  decide +kernel

theorem k15_211 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).2 2).2 3).2 1).2 2).2 3).2 1).2 2).2 3).1 3).1
      166155718149315660687091523707212450258617691130669559799719328468888253450087047245547373739127698031067396473896).isSome = true := by
  decide +kernel

theorem k15_212 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).2 2).2 3).2 1).2 2).2 3).2 1).2 2).2 3).1 3).2
      3621189679939197869303871759258223138694499405992725448287731732829003572321786189365452341274597726200479440752984).isSome = true := by
  decide +kernel

theorem k15_213 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).2 2).2 3).2 1).2 2).2 3).2 1).2 2).2 3).2
      1800087173871429071067199802198926588874936779118911425870827596558326650023167162146658760691464313138565518758624428913555054979474718232798658384572968162883842313188753642430888671114806024462501581899874159030743920388484381037461456227).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChB016
