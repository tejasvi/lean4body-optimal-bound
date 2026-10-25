module

public import C4Check

public section

/-! Pieces of cell `8` of the chart root grid B: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChB001

theorem k8_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).1 2).2 3).2 1).2 2).1 3).1
      1219891089381931842463846678129787368408753252131153103179935172261785162728004174149016665066161308410052592976259221966288833251069544360329459914304556172526703942823818070895318232513242484616773895119633292021640657140675502043169).isSome = true := by
  decide +kernel

theorem k8_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).1 2).2 3).2 1).2 2).1 3).2
      1291111280798368261108836563760356862930667664598589424171126012423912988403857025369419117034498111211603521569).isSome = true := by
  decide +kernel

theorem k8_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).1 2).2 3).2 1).2 2).2 3).1 1).1
      538843738282719674426003019976761248581200840244509654262630778408584386804876636877330661995503501745723175272).isSome = true := by
  decide +kernel

theorem k8_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).1 2).2 3).2 1).2 2).2 3).1 1).2
      123074052993983621790685149151090295074178688420905161188346965466023975870001479077934853254166300242009613433128).isSome = true := by
  decide +kernel

theorem k8_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).1 2).2 3).2 1).2 2).2 3).2
      426756586939739478483343946867683350900393762482006110919341135332143207289759660925748207823762643437788382408571779501895014790807696076089593651200513029993284168334336439883989167228434852414350536492411224267972339358606719265540350526881).isSome = true := by
  decide +kernel

theorem k8_34 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).2 1).1 1).1 2).1
      0).isSome = true := by
  decide +kernel

theorem k8_35 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).2 1).1 1).1 2).2 3).1 2).1
      1291243175189147784776158932458410140250873871994776450446738167613441878925198099475707357251498384093842698657202758173).isSome = true := by
  decide +kernel

theorem k8_36 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).2 1).1 1).1 2).2 3).1 2).2 3).1 2).1
      1441418012340494407007954464781813539896556513773976772438613943205339024460416518494345914037260888478822346913).isSome = true := by
  decide +kernel

theorem k8_37 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).2 1).1 1).1 2).2 3).1 2).2 3).1 2).2
      173314075926029287109324898630994109698343048353116405898602322050742621181413716949525168077234159938936252179016).isSome = true := by
  decide +kernel

theorem k8_38 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).2 1).1 1).1 2).2 3).1 2).2 3).2
      2033250738981387357142574624542411847866681702791719112871260304867597872539128304492270456123701239538159685153).isSome = true := by
  decide +kernel

theorem k8_39 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 8) 1).2 1).1 1).1 2).2 3).2
      0).isSome = true := by
  decide +kernel

theorem k8_40 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chBCellBox 8) 1).2 1).1 1).2
      0).isSome = true := by
  decide +kernel

theorem k8_41 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chBCellBox 8) 1).2 1).2
      0).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChB001
