module

public import C4Check

public section

/-! Pieces of cell `8` of the direct root grid: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_Dir009

theorem k8_77 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).2 3).2 3).2 1).2 2).1 1).2 2).1 3).2
      273922555923219801050663798912161730401835706847179947355846831609163049696707758665358608497520051235251688890138520120696163808488892478215929154372609380164225228470953579158475845607949874913246108581097782753065513236433828605859).isSome = true := by
  decide +kernel

theorem k8_78 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).2 3).2 3).2 1).2 2).1 1).2 2).2 3).1
      108048305994612933505664099898569966986538166856733676533734242651174279982185144623432902940627876321246660867).isSome = true := by
  decide +kernel

theorem k8_79 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).2 3).2 3).2 1).2 2).1 1).2 2).2 3).2
      426754144656450927084260868326556900688883363835152501533358629907116336865023461094469901289999607060086321165411989136698233721955179562854933537591175981391021247253498760105493167603707191778375540687854850325674484136589766538762929034147).isSome = true := by
  decide +kernel

theorem k8_80 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).2 3).2 3).2 1).2 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k8_81 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).2 3).2 3).2 1).2 2).2 3).2 1).1
      71424743220271934864358903234038684061669636458526947610060989092498057184087725373077128219143113417555334681114601842093728936521182033105187441577275775878193467697321546568245020683406818426557293289961064442308477472702889854019).isSome = true := by
  decide +kernel

theorem k8_82 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).2 3).2 3).2 1).2 2).2 3).2 1).2
      2231827976109774114291881487604432274300895500451296199471367241669106453820282840855648000800902785095966759231011974712603380996157266287883048282422540524664827468380107900234459801256499724915625508094913438585021262618875082658).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_Dir009
