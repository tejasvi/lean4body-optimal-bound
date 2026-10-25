module

public import C4Check

public section

/-! Cells `15 ≤ n < 16` of the chart root grid C: `decide +kernel` checks that `checkBoxH2` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChC008

theorem k15_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).1 2).1 3).1 3).1
      89508682419047713565474222618338694835482065047713091084569536005674764733404507211605863862640189011540542812040).isSome = true := by
  decide +kernel

theorem k15_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).1 2).1 3).1 3).2
      576420434699951232415155128026139433352124435792659921182027971601474084042378266644242832835758501943388270472).isSome = true := by
  decide +kernel

theorem k15_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).1 2).1 3).2 3).1
      322777833758085907845934833963425339752455859143103339617381996754644197181519293907445256125207202064011342216).isSome = true := by
  decide +kernel

theorem k15_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).1 2).1 3).2 3).2
      567026260714575101564962073355889836013895036993857269292813683586793512887555454884812765082579473254374322568).isSome = true := by
  decide +kernel

theorem k15_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).1 2).2 3).1 3).1
      123027082157183678649933343712734956498448916491201544334985326457441299460646291918911116943467018031777169605928).isSome = true := by
  decide +kernel

theorem k15_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).1 2).2 3).1 3).2
      332172003370190917288059436176706412500755437333709649097440528300550628704700004037123007605017644423992018216).isSome = true := by
  decide +kernel

theorem k15_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).1 2).2 3).2
      360863429951716952074646956208850341879164707728825100579555481166157771827217400393142125546682923959445605087958358485776520730946848696520877707708055885020250176438643353472676388679502281254666200177154049907543644897256081593507).isSome = true := by
  decide +kernel

theorem k15_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).2 2).1 3).1 3).1
      147266390156067223761332749300550442646627536812476601465912310910965751842748326536912009360814350609379169348264).isSome = true := by
  decide +kernel

theorem k15_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).2 2).1 3).1 3).2
      125366230569097511977482876797266991816610349624979912181089218373050562324286065402112813783657792511766945189064).isSome = true := by
  decide +kernel

theorem k15_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).2 2).1 3).2 3).1
      341566173061105302273265235657386277768705033270275534575169911399978483238095743973611552101555603158411564392).isSome = true := by
  decide +kernel

theorem k15_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).2 2).1 3).2 3).2
      585814599999891435479384349197856159525403718261450162860974671896705494269314715829408156271918834792948815208).isSome = true := by
  decide +kernel

theorem k15_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).2 2).2 3).1 3).1
      120399063005935512394821014682879401566712986250746983108416815003541177612799369614610302827000541346448986137256).isSome = true := by
  decide +kernel

theorem k15_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).2 2).2 3).1 3).2
      118217266944517191546235924585510657455448699152844013050480459036019613708325702945519252461146118541436836700840).isSome = true := by
  decide +kernel

theorem k15_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).2 2).2 3).2 3).1
      322777830231622574849880953149766082821374861005966426658031414815114287803184181087351309885392414321194132136).isSome = true := by
  decide +kernel

theorem k15_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).1 1).2 2).2 3).2 3).2
      576420427854129868756740661069857037613486852631675399690342121899098781594077141175503536187555199693059351208).isSome = true := by
  decide +kernel

theorem k15_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).1 3).1 3).1
      304972782028687947209556880465302003465029213093417309058044219211556738415839091899152807262951659473380127306838023775376235823609394740724202282417361178982708532502161776004368461901265329024572913094945490511867509325599917048995).isSome = true := by
  decide +kernel

theorem k15_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).1 3).1 3).2
      190355100918440403068258428659733792598122400837660972817160395789285403887744317495470618160981856059986161488872).isSome = true := by
  decide +kernel

theorem k15_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).1 3).2 3).1
      183177954783387840771031278578015452899510587221923622295733727539853416872166985714644732306468305991314049933032).isSome = true := by
  decide +kernel

theorem k15_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).1 3).2 3).2
      332171999871888435348152414049247654492136063575674259266005842658752546187202454571527888098563728473568780008).isSome = true := by
  decide +kernel

theorem k15_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).2 3).1 3).1 1).1
      350960344081047911482235739425582459930548687196666797405508864915225399940035087298715923271560428040953232872).isSome = true := by
  decide +kernel

theorem k15_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).2 3).1 3).1 1).2
      159128878737171530752222410564872205265189800350777035721350923065478972049414504730079356403396029993900313773128).isSome = true := by
  decide +kernel

theorem k15_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).2 3).1 3).2
      118001201025830792846335131334548545792080584175233272677721662045594573474919457290227059768546224210841218843720).isSome = true := by
  decide +kernel

theorem k15_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).2 3).2 3).1
      190364495084638756508180764410895396526391679802990258903308473021983267682294396468313793186280506534845711877192).isSome = true := by
  decide +kernel

theorem k15_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).1 2).2 3).2 3).2
      322777827866931134143001288349823317849998085215058498325121292742327676322259193405436709297963132134320407624).isSome = true := by
  decide +kernel

theorem k15_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).1 3).1 3).1 1).1
      529449582494039251598121195382541593683574414757826629774253027951122224593164157288792097238090844008120091784).isSome = true := by
  decide +kernel

theorem k15_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).1 3).1 3).1 1).2
      20175674727409033331390114144537202263842943081979393637999054190886051241433276177549504110442159718117204981867722472).isSome = true := by
  decide +kernel

theorem k15_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).1 3).1 3).2
      632394666824732754878010763063733904493994871240264681315905478552546693997278379504659712322835745226605769755225544).isSome = true := by
  decide +kernel

theorem k15_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).1 3).2 3).1
      120446033853847577792934091764450437902545685080249820469510812282536512346009598226582131538116416402432762525416).isSome = true := by
  decide +kernel

theorem k15_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).1 3).2 3).2
      178377533741494957162862139892642135260345698410658561701370182109534347166985236810063235675099739574511561783016).isSome = true := by
  decide +kernel

theorem k15_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).2 3).1 3).1 2).1
      166381178232826067494459383465131451172043399861091089027506536052157164786346331370646808643612663249142190599784).isSome = true := by
  decide +kernel

theorem k15_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).2 3).1 3).1 2).2
      173323470105983602121426102411025244531499388137158501800195244564704419568298652849027599876935056632925821950760).isSome = true := by
  decide +kernel

theorem k15_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).2 3).1 3).2
      134913056163410472315715887810890405071290837629847512295892568107496595417072788654086067198896548121794917209640).isSome = true := by
  decide +kernel

theorem k15_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).2 3).2 3).1
      115596293418489158358469339988840640266537695288694951948303426435620293776923202587434268010909953039160743433768).isSome = true := by
  decide +kernel

theorem k15_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 15) 1).2 1).2 2).2 3).2 3).2
      185554679872884558011898525009228407744693859669615540173582107322280915128998772053261307030781304970995741103656).isSome = true := by
  decide +kernel

theorem cover : Cover2 (chModeTFM 7) chCCellBox 15 16 :=
  (Cover2.one (box := chCCellBox) (n := 15)
      (.split 1 (.split 1 (.split 2 (.split 3 (.split 3 (.leaf _ k15_0) (.leaf _ k15_1)) (.split 3 (.leaf _ k15_2) (.leaf _ k15_3))) (.split 3 (.split 3 (.leaf _ k15_4) (.leaf _ k15_5)) (.leaf _ k15_6))) (.split 2 (.split 3 (.split 3 (.leaf _ k15_7) (.leaf _ k15_8)) (.split 3 (.leaf _ k15_9) (.leaf _ k15_10))) (.split 3 (.split 3 (.leaf _ k15_11) (.leaf _ k15_12)) (.split 3 (.leaf _ k15_13) (.leaf _ k15_14))))) (.split 1 (.split 2 (.split 3 (.split 3 (.leaf _ k15_15) (.leaf _ k15_16)) (.split 3 (.leaf _ k15_17) (.leaf _ k15_18))) (.split 3 (.split 3 (.split 1 (.leaf _ k15_19) (.leaf _ k15_20)) (.leaf _ k15_21)) (.split 3 (.leaf _ k15_22) (.leaf _ k15_23)))) (.split 2 (.split 3 (.split 3 (.split 1 (.leaf _ k15_24) (.leaf _ k15_25)) (.leaf _ k15_26)) (.split 3 (.leaf _ k15_27) (.leaf _ k15_28))) (.split 3 (.split 3 (.split 2 (.leaf _ k15_29) (.leaf _ k15_30)) (.leaf _ k15_31)) (.split 3 (.leaf _ k15_32) (.leaf _ k15_33)))))))

end C4.Cert.Gen2_ChC008
