module

public import C4Check
public import C4Cert.Gen2_ChB000
public import C4Cert.Gen2_ChB001
public import C4Cert.Gen2_ChB002
public import C4Cert.Gen2_ChB003
public import C4Cert.Gen2_ChB004
public import C4Cert.Gen2_ChB005
public import C4Cert.Gen2_ChB006
public import C4Cert.Gen2_ChB007
public import C4Cert.Gen2_ChB008

public section

/-! Cells `0 ≤ n < 13` of the chart root grid B: `decide +kernel` checks that `checkBoxH2` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChB009

theorem c0 : allCells (cellOK (chModeTFM 7) chBCellBox) 0 4 [
    0, 410542584, 1759199650296,
    12322675565543765070453826777973595989563534468050734375094823124529418735642001845502013249066263009239881212495858644936063293837] = true := by
  decide +kernel

theorem k4_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chBCellBox 4) 1).1 1).1 2).1
      205188388167924957907506243399753416587897812721576339503830460666167498308352684694676557135521785394470637323212993259618331004973).isSome = true := by
  decide +kernel

theorem k4_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 4) 1).1 1).1 2).2 3).1 2).1
      120937993542337362495153399859732819856424761334809624348322262211484933504857438523866207267488408147517175312285725).isSome = true := by
  decide +kernel

theorem k4_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 4) 1).1 1).1 2).2 3).1 2).2 3).1
      165684730689535793371358270717014036197508615244510152953152837838791449972717596753041346159488117727038578642072651755214558671007952619328428263773003306726817964693425308030772288507045500525782489624651963480037491185171231870033545).isSome = true := by
  decide +kernel

theorem k4_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 4) 1).1 1).1 2).2 3).1 2).2 3).2
      645564934180365161034186944320315650387648396588827441031331810115319807805803566262396941416923489273424752642591122849).isSome = true := by
  decide +kernel

theorem k4_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chBCellBox 4) 1).1 1).1 2).2 3).2
      25).isSome = true := by
  decide +kernel

theorem k4_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chBCellBox 4) 1).1 1).2
      0).isSome = true := by
  decide +kernel

theorem k4_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (chBCellBox 4) 1).2
      0).isSome = true := by
  decide +kernel

theorem c2 : allCells (cellOK (chModeTFM 7) chBCellBox) 5 7 [
    0, 408] = true := by
  decide +kernel

theorem k7_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chBCellBox 7) 1).1 3).1
      408).isSome = true := by
  decide +kernel

theorem k7_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chBCellBox 7) 1).1 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k7_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).1 3).2 2).2 1).1
      130208610346552382206357913129513189147502882773560717212296117992316993358544630795505864742425447897857271555465999840186444880311041132532278927632605900865569671792621834113469641949988488069929540636789411070317300705460641156172739657987).isSome = true := by
  decide +kernel

theorem k7_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).1 3).2 2).2 1).2 2).1
      49538).isSome = true := by
  decide +kernel

theorem k7_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).1 3).2 2).2 1).2 2).2 3).1
      385).isSome = true := by
  decide +kernel

theorem k7_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).1 3).2 2).2 1).2 2).2 3).2 1).1
      80697276086501855763199492531082972527697550976721475204103897666185096434612758331555784388153709961745718686684426280).isSome = true := by
  decide +kernel

theorem k7_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).1 3).2 2).2 1).2 2).2 3).2 1).2
      13464716171479121450787538295805824096784896757589894341313515854229167785725614845034030782924583979345210910807798572023392542037993640323344411259134558925494627680720449460571596117908544119819680887285297744921006071019432130626457614).isSome = true := by
  decide +kernel

theorem k7_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chBCellBox 7) 1).2 2).1
      209027).isSome = true := by
  decide +kernel

theorem k7_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chBCellBox 7) 1).2 2).2 3).1
      6685058).isSome = true := by
  decide +kernel

theorem k7_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).2 2).2 3).2 1).1 2).1
      3948819820794082228312398997492248531654101742273580990785487470748227942566494776896397834352583247218042898185651331).isSome = true := by
  decide +kernel

theorem k7_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).2 2).2 3).2 1).1 2).2 3).1
      437015003625407480705514038848393870722101510811437353854095447535855941173594869651176256573429556509386131607791110918566142696502448166540128212122312785907367134239858848398526905089845652402606098335342351127348322666983897128702210732474627).isSome = true := by
  decide +kernel

theorem k7_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).2 2).2 3).2 1).1 2).2 3).2 1).1 2).1
      40349619352926101849912127740459970204445488603024798550832828806743458558306619406780910587445097511824222770480680648).isSome = true := by
  decide +kernel

theorem k7_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).2 2).2 3).2 1).1 2).2 3).2 1).1 2).2
      130122029287315333502832526190821765070911208305872674041443668337232825590609653207973914656941663476462235853384).isSome = true := by
  decide +kernel

theorem k7_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).2 2).2 3).2 1).1 2).2 3).2 1).2
      1707168004512300958455495734840813289379048639035240527518169712311535967960204006498106314085060437439015929840454261981408122417562567282410675690740003152637944292850459939318583528758958513465630634503844238136257016924056552224203570457222).isSome = true := by
  decide +kernel

theorem k7_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chBCellBox 7) 1).2 2).2 3).2 1).2
      2644708217203637688424391820590561421636247406360003973824938362061767163607544851283740491042300418593507059440734531948693).isSome = true := by
  decide +kernel

theorem c5 : allCells (cellOK (chModeTFM 7) chBCellBox) 9 11 [
    4226381442530179360390248369303762245228435937708859705299494654270130524730356957954577475543305134167177469138771787016342831534450884611891187419152468532452990299683575227592980607813994313050708915458094372686420012317211850368291209343534570132737788600756426278617,
    3] = true := by
  decide +kernel

theorem cover : Cover2 (chModeTFM 7) chBCellBox 0 13 :=
  (Cover2.cells c0).trans <|
  (Cover2.one (box := chBCellBox) (n := 4)
      (.split 1 (.split 1 (.split 2 (.leaf _ k4_0) (.split 3 (.split 2 (.leaf _ k4_1) (.split 3 (.leaf _ k4_2) (.leaf _ k4_3))) (.leaf _ k4_4))) (.leaf _ k4_5)) (.leaf _ k4_6))).trans <|
  (Cover2.cells c2).trans <|
  (Cover2.one (box := chBCellBox) (n := 7)
      (.split 1 (.split 3 (.leaf _ k7_0) (.split 2 (.leaf _ k7_1) (.split 1 (.leaf _ k7_2) (.split 2 (.leaf _ k7_3) (.split 3 (.leaf _ k7_4) (.split 1 (.leaf _ k7_5) (.leaf _ k7_6))))))) (.split 2 (.leaf _ k7_7) (.split 3 (.leaf _ k7_8) (.split 1 (.split 2 (.leaf _ k7_9) (.split 3 (.leaf _ k7_10) (.split 1 (.split 2 (.leaf _ k7_11) (.leaf _ k7_12)) (.leaf _ k7_13)))) (.leaf _ k7_14)))))).trans <|
  (Cover2.one (box := chBCellBox) (n := 8)
      (.split 1 (.split 2 (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB000.k8_0) (.split 2 (.leaf _ C4.Cert.Gen2_ChB000.k8_1) (.split 3 (.leaf _ C4.Cert.Gen2_ChB000.k8_2) (.split 1 (.leaf _ C4.Cert.Gen2_ChB000.k8_3) (.leaf _ C4.Cert.Gen2_ChB000.k8_4))))) (.split 1 (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB000.k8_5) (.leaf _ C4.Cert.Gen2_ChB000.k8_6)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB000.k8_7) (.leaf _ C4.Cert.Gen2_ChB000.k8_8))) (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB000.k8_9) (.split 3 (.leaf _ C4.Cert.Gen2_ChB000.k8_10) (.leaf _ C4.Cert.Gen2_ChB000.k8_11))) (.leaf _ C4.Cert.Gen2_ChB000.k8_12)))) (.split 3 (.split 1 (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB000.k8_13) (.leaf _ C4.Cert.Gen2_ChB000.k8_14)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB000.k8_15) (.leaf _ C4.Cert.Gen2_ChB000.k8_16))) (.split 2 (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB000.k8_17) (.leaf _ C4.Cert.Gen2_ChB000.k8_18)) (.split 1 (.leaf _ C4.Cert.Gen2_ChB000.k8_19) (.leaf _ C4.Cert.Gen2_ChB000.k8_20))) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB000.k8_21) (.split 2 (.leaf _ C4.Cert.Gen2_ChB000.k8_22) (.leaf _ C4.Cert.Gen2_ChB000.k8_23))) (.split 1 (.leaf _ C4.Cert.Gen2_ChB000.k8_24) (.leaf _ C4.Cert.Gen2_ChB000.k8_25))))) (.split 1 (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB000.k8_26) (.leaf _ C4.Cert.Gen2_ChB000.k8_27)) (.leaf _ C4.Cert.Gen2_ChB000.k8_28)) (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB001.k8_29) (.leaf _ C4.Cert.Gen2_ChB001.k8_30)) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB001.k8_31) (.leaf _ C4.Cert.Gen2_ChB001.k8_32)) (.leaf _ C4.Cert.Gen2_ChB001.k8_33)))))) (.split 1 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB001.k8_34) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChB001.k8_35) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChB001.k8_36) (.leaf _ C4.Cert.Gen2_ChB001.k8_37)) (.leaf _ C4.Cert.Gen2_ChB001.k8_38))) (.leaf _ C4.Cert.Gen2_ChB001.k8_39))) (.leaf _ C4.Cert.Gen2_ChB001.k8_40)) (.leaf _ C4.Cert.Gen2_ChB001.k8_41)))).trans <|
  (Cover2.cells c5).trans <|
  (Cover2.one (box := chBCellBox) (n := 11)
      (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_0) (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_1) (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_2) (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_3) (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_4) (.leaf _ C4.Cert.Gen2_ChB002.k11_5)))) (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_6) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB002.k11_7) (.leaf _ C4.Cert.Gen2_ChB002.k11_8)) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_9) (.leaf _ C4.Cert.Gen2_ChB002.k11_10)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_11) (.leaf _ C4.Cert.Gen2_ChB002.k11_12)))))))) (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_13) (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_14) (.split 1 (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_15) (.split 1 (.leaf _ C4.Cert.Gen2_ChB002.k11_16) (.leaf _ C4.Cert.Gen2_ChB002.k11_17))) (.split 3 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_18) (.leaf _ C4.Cert.Gen2_ChB002.k11_19)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_20) (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_21) (.leaf _ C4.Cert.Gen2_ChB002.k11_22)))) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_23) (.leaf _ C4.Cert.Gen2_ChB002.k11_24)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_25) (.leaf _ C4.Cert.Gen2_ChB002.k11_26))))) (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_27) (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_28) (.leaf _ C4.Cert.Gen2_ChB002.k11_29)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_30) (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_31) (.leaf _ C4.Cert.Gen2_ChB002.k11_32))))) (.split 3 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB002.k11_33) (.split 3 (.leaf _ C4.Cert.Gen2_ChB002.k11_34) (.leaf _ C4.Cert.Gen2_ChB003.k11_35))) (.split 2 (.leaf _ C4.Cert.Gen2_ChB003.k11_36) (.split 3 (.leaf _ C4.Cert.Gen2_ChB003.k11_37) (.leaf _ C4.Cert.Gen2_ChB003.k11_38)))) (.split 1 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChB003.k11_39) (.leaf _ C4.Cert.Gen2_ChB003.k11_40)) (.leaf _ C4.Cert.Gen2_ChB003.k11_41)) (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB003.k11_42) (.leaf _ C4.Cert.Gen2_ChB003.k11_43)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB003.k11_44) (.leaf _ C4.Cert.Gen2_ChB003.k11_45))))))))))).trans <|
  (Cover2.one (box := chBCellBox) (n := 12)
      (.split 1 (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB004.k12_0) (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_1) (.leaf _ C4.Cert.Gen2_ChB004.k12_2))) (.split 2 (.leaf _ C4.Cert.Gen2_ChB004.k12_3) (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_4) (.split 1 (.leaf _ C4.Cert.Gen2_ChB004.k12_5) (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_6) (.leaf _ C4.Cert.Gen2_ChB004.k12_7)))))) (.split 1 (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_8) (.split 1 (.leaf _ C4.Cert.Gen2_ChB004.k12_9) (.leaf _ C4.Cert.Gen2_ChB004.k12_10))) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB004.k12_11) (.leaf _ C4.Cert.Gen2_ChB004.k12_12)) (.leaf _ C4.Cert.Gen2_ChB004.k12_13))) (.split 2 (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB004.k12_14) (.leaf _ C4.Cert.Gen2_ChB004.k12_15)) (.split 1 (.leaf _ C4.Cert.Gen2_ChB004.k12_16) (.split 2 (.leaf _ C4.Cert.Gen2_ChB004.k12_17) (.leaf _ C4.Cert.Gen2_ChB004.k12_18)))) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB004.k12_19) (.split 2 (.leaf _ C4.Cert.Gen2_ChB004.k12_20) (.leaf _ C4.Cert.Gen2_ChB004.k12_21))) (.split 1 (.leaf _ C4.Cert.Gen2_ChB004.k12_22) (.leaf _ C4.Cert.Gen2_ChB004.k12_23)))))) (.split 3 (.split 1 (.split 2 (.split 3 (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_24) (.leaf _ C4.Cert.Gen2_ChB004.k12_25)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_26) (.leaf _ C4.Cert.Gen2_ChB004.k12_27))) (.split 3 (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_28) (.leaf _ C4.Cert.Gen2_ChB004.k12_29)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_30) (.leaf _ C4.Cert.Gen2_ChB004.k12_31)))) (.split 2 (.split 3 (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB004.k12_32) (.leaf _ C4.Cert.Gen2_ChB004.k12_33)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB005.k12_34) (.leaf _ C4.Cert.Gen2_ChB005.k12_35))) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChB005.k12_36) (.leaf _ C4.Cert.Gen2_ChB005.k12_37)) (.leaf _ C4.Cert.Gen2_ChB005.k12_38))) (.split 3 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChB005.k12_39) (.leaf _ C4.Cert.Gen2_ChB005.k12_40)) (.leaf _ C4.Cert.Gen2_ChB005.k12_41)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB005.k12_42) (.leaf _ C4.Cert.Gen2_ChB005.k12_43))))) (.split 1 (.split 2 (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChB005.k12_44) (.leaf _ C4.Cert.Gen2_ChB005.k12_45)) (.leaf _ C4.Cert.Gen2_ChB005.k12_46)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB005.k12_47) (.leaf _ C4.Cert.Gen2_ChB005.k12_48))) (.split 2 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChB005.k12_49) (.leaf _ C4.Cert.Gen2_ChB005.k12_50)) (.leaf _ C4.Cert.Gen2_ChB005.k12_51)) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChB005.k12_52) (.leaf _ C4.Cert.Gen2_ChB005.k12_53)) (.leaf _ C4.Cert.Gen2_ChB005.k12_54)))))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB005.k12_55) (.split 3 (.leaf _ C4.Cert.Gen2_ChB005.k12_56) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB005.k12_57) (.leaf _ C4.Cert.Gen2_ChB005.k12_58)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB005.k12_59) (.leaf _ C4.Cert.Gen2_ChB005.k12_60))))) (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB005.k12_61) (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB005.k12_62) (.leaf _ C4.Cert.Gen2_ChB005.k12_63)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB005.k12_64) (.leaf _ C4.Cert.Gen2_ChB005.k12_65)))) (.split 3 (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB005.k12_66) (.leaf _ C4.Cert.Gen2_ChB006.k12_67)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB006.k12_68) (.leaf _ C4.Cert.Gen2_ChB006.k12_69))) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB006.k12_70) (.leaf _ C4.Cert.Gen2_ChB006.k12_71)) (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB006.k12_72) (.leaf _ C4.Cert.Gen2_ChB006.k12_73)) (.leaf _ C4.Cert.Gen2_ChB006.k12_74)))))) (.split 1 (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB006.k12_75) (.leaf _ C4.Cert.Gen2_ChB006.k12_76)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB006.k12_77) (.leaf _ C4.Cert.Gen2_ChB006.k12_78))) (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB006.k12_79) (.leaf _ C4.Cert.Gen2_ChB006.k12_80)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB006.k12_81) (.leaf _ C4.Cert.Gen2_ChB006.k12_82)))) (.split 3 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB006.k12_83) (.leaf _ C4.Cert.Gen2_ChB006.k12_84)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB006.k12_85) (.leaf _ C4.Cert.Gen2_ChB006.k12_86))) (.split 2 (.split 1 (.leaf _ C4.Cert.Gen2_ChB006.k12_87) (.leaf _ C4.Cert.Gen2_ChB006.k12_88)) (.leaf _ C4.Cert.Gen2_ChB006.k12_89)))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB006.k12_90) (.leaf _ C4.Cert.Gen2_ChB006.k12_91)) (.leaf _ C4.Cert.Gen2_ChB006.k12_92)) (.leaf _ C4.Cert.Gen2_ChB006.k12_93)) (.split 3 (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB006.k12_94) (.leaf _ C4.Cert.Gen2_ChB006.k12_95)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB006.k12_96) (.leaf _ C4.Cert.Gen2_ChB006.k12_97))) (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB007.k12_98) (.leaf _ C4.Cert.Gen2_ChB007.k12_99)) (.leaf _ C4.Cert.Gen2_ChB007.k12_100)))))) (.split 3 (.split 1 (.split 2 (.split 3 (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_101) (.leaf _ C4.Cert.Gen2_ChB007.k12_102)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_103) (.leaf _ C4.Cert.Gen2_ChB007.k12_104))) (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB007.k12_105) (.leaf _ C4.Cert.Gen2_ChB007.k12_106)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB007.k12_107) (.leaf _ C4.Cert.Gen2_ChB007.k12_108)))) (.split 3 (.split 3 (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_109) (.leaf _ C4.Cert.Gen2_ChB007.k12_110)) (.leaf _ C4.Cert.Gen2_ChB007.k12_111)) (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChB007.k12_112) (.leaf _ C4.Cert.Gen2_ChB007.k12_113)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB007.k12_114) (.leaf _ C4.Cert.Gen2_ChB007.k12_115))))) (.split 2 (.split 3 (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_116) (.leaf _ C4.Cert.Gen2_ChB007.k12_117)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB007.k12_118) (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_119) (.leaf _ C4.Cert.Gen2_ChB007.k12_120)))) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_121) (.leaf _ C4.Cert.Gen2_ChB007.k12_122)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_123) (.leaf _ C4.Cert.Gen2_ChB007.k12_124)))) (.split 3 (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_125) (.leaf _ C4.Cert.Gen2_ChB007.k12_126)) (.split 3 (.leaf _ C4.Cert.Gen2_ChB007.k12_127) (.leaf _ C4.Cert.Gen2_ChB007.k12_128))) (.split 3 (.split 3 (.leaf _ C4.Cert.Gen2_ChB008.k12_129) (.leaf _ C4.Cert.Gen2_ChB008.k12_130)) (.leaf _ C4.Cert.Gen2_ChB008.k12_131))))) (.split 1 (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ C4.Cert.Gen2_ChB008.k12_132) (.leaf _ C4.Cert.Gen2_ChB008.k12_133)) (.leaf _ C4.Cert.Gen2_ChB008.k12_134)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB008.k12_135) (.leaf _ C4.Cert.Gen2_ChB008.k12_136))) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChB008.k12_137) (.leaf _ C4.Cert.Gen2_ChB008.k12_138)) (.leaf _ C4.Cert.Gen2_ChB008.k12_139))) (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChB008.k12_140) (.leaf _ C4.Cert.Gen2_ChB008.k12_141)) (.leaf _ C4.Cert.Gen2_ChB008.k12_142)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB008.k12_143) (.leaf _ C4.Cert.Gen2_ChB008.k12_144))) (.split 3 (.split 3 (.leaf _ C4.Cert.Gen2_ChB008.k12_145) (.leaf _ C4.Cert.Gen2_ChB008.k12_146)) (.split 2 (.leaf _ C4.Cert.Gen2_ChB008.k12_147) (.leaf _ C4.Cert.Gen2_ChB008.k12_148)))))))))

end C4.Cert.Gen2_ChB009
