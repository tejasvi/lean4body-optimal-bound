module

public import C4Check

public section

/-! Pieces of cell `19` of the chart root grid C: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChC017

theorem k19_202 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 19) 1).2 1).2 2).2 3).2 3).2 3).2 3).2 1).1 2).1
      306138250253655858619655085142950844637090809209425925696115660912149762763470920875584782503209641961002289507400).isSome = true := by
  decide +kernel

theorem k19_203 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 19) 1).2 1).2 2).2 3).2 3).2 3).2 3).2 1).1 2).2
      289116013609679123727370283864129977409264364295454927797053253330520201573895816041584051660981046842970267630504).isSome = true := by
  decide +kernel

theorem k19_204 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 19) 1).2 1).2 2).2 3).2 3).2 3).2 3).2 1).2 1).1
      245602216637690012468154597680119763945885533131413355074967891777235409687618172857405136343158526404688784248136).isSome = true := by
  decide +kernel

theorem k19_205 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 19) 1).2 1).2 2).2 3).2 3).2 3).2 3).2 1).2 1).2
      250440214358001173061250347196323354408688657049045010840912431006851057451986745088963166512940474367071363647048).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChC017
