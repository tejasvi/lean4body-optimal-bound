module

public import C4Check

public section

/-! Cells `21 ≤ n < 22` of the chart root grid C: `decide +kernel` checks that `checkBoxH2` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChC030

theorem k21_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).1 2).1 3).1 3).1
      127808714852552744703867557224327275717907308824907185092204567638752797632994069053288433078583266930816549140712).isSome = true := by
  decide +kernel

theorem k21_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).1 2).1 3).1 3).2
      313383660020210868766002024878562267609674157263453082522480906924841098084152672161952874329531404496784210152).isSome = true := by
  decide +kernel

theorem k21_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).1 2).1 3).2
      354653356265077716524287374962654926864053902931023996367358906844552657876645593124075101556124872157504910778119728784841656310443676998322347325874142643193629772988040100383713806564856859620318616056920157453315932339903540814755).isSome = true := by
  decide +kernel

theorem k21_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).1 2).2 3).1 3).1
      135004649323072230382474468500029023468008056749195811855062682104218324413307432845179979127577237757746846077736).isSome = true := by
  decide +kernel

theorem k21_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).1 2).2 3).1 3).2
      313383657370561670585079388419879673405986296014935620775501426352374482194497514598384564232279597787206751016).isSome = true := by
  decide +kernel

theorem k21_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).1 2).2 3).2
      360863427325429154893948003341406067580121580574906052314727455499266070617490959657086791308163846981922644060636352822582335689268449155704516896969621619968134284950061182116944007991219193996371963050970889358541522525389189172387).isSome = true := by
  decide +kernel

theorem k21_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).2 2).1 3).1 3).1
      123045870493631173872020994184141678794848673030472998606693643149140876161692974852475736998895721351756335157384).isSome = true := by
  decide +kernel

theorem k21_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).2 2).1 3).1 3).2
      125403807245250822486881622533063874212164223306990636389706116785288141442806698613472441599766514110813850570888).isSome = true := by
  decide +kernel

theorem k21_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).2 2).1 3).2 3).1
      313383657766180644414330463149337572579216816946935850112985894604872374631873191983334731496174802366947823752).isSome = true := by
  decide +kernel

theorem k21_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).2 2).1 3).2 3).2
      567026255722312025443499243977390303839157116530234453423001105361607531693167855379532075472038144413175812232).isSome = true := by
  decide +kernel

theorem k21_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).2 2).2 3).1 3).1
      130223016623639594239785141312037027876071725102947305347163042943726295414193028632503519719207210545692763499720).isSome = true := by
  decide +kernel

theorem k21_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).2 2).2 3).1 3).2
      132599741716407481642497793406756454043251783126155619004136149012229198180590166100015063953857589361767295593672).isSome = true := by
  decide +kernel

theorem k21_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).2 2).2 3).2 3).1
      303989485359042616151333537512068562163294309461432875755619926494836731682504965043540242584291986777212529864).isSome = true := by
  decide +kernel

theorem k21_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).1 1).2 2).2 3).2 3).2
      567026253957200690951063559315662867827336142709912252636694732767503170189862259117987375841089975200056552648).isSome = true := by
  decide +kernel

theorem k21_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).1 2).1 3).1 3).1
      125227666552049953756893037618648909492525877214833464346325450068646469094647290991044765874866228079436674599016).isSome = true := by
  decide +kernel

theorem k21_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).1 2).1 3).1 3).2
      120650357056748930642346544651918129266364036906114241186579193392815415258237154976399968216748010599757366659176).isSome = true := by
  decide +kernel

theorem k21_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).1 2).1 3).2 3).1
      350960338146079772167663248834805488823236654880298897111964033693548909216303872895499497155441404356396517480).isSome = true := by
  decide +kernel

theorem k21_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).1 2).1 3).2 3).2
      313383655867510311413176160209440165996113988145965849637211401104137839259059672358855931060147440335072888936).isSome = true := by
  decide +kernel

theorem k21_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).1 2).2 3).1 3).1
      127876822582580469713549948100966448372071149022929282643544674902696656205699073120191495090608501051935762625352).isSome = true := by
  decide +kernel

theorem k21_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).1 2).2 3).1 3).2
      127827503187376274613857033877389500222524819648052677040198083422492528309420631346991969344649214303279028056904).isSome = true := by
  decide +kernel

theorem k21_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).1 2).2 3).2 3).1
      332171995550632872567082513159147118153761882630214710318846745534097844243574311583461463218289881254413611848).isSome = true := by
  decide +kernel

theorem k21_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).1 2).2 3).2 3).2
      595208764179959270233037564706350742744303026704070713290943045596476591555278090930000688659092570478781018952).isSome = true := by
  decide +kernel

theorem k21_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).1 3).1 3).1 1).1
      161524392168132066050242349357631445065970431988569600826934829769155112005563243262328437180331596750936016989032).isSome = true := by
  decide +kernel

theorem k21_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).1 3).1 3).1 1).2
      168504260723697696390974981244129582643449071470812049434001545694261418409159514231139783281561038791425988679016).isSome = true := by
  decide +kernel

theorem k21_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).1 3).1 3).2
      127651362495103620409031002119608380775522306021649522453948780447326975698883946804523274870105572730204074333544).isSome = true := by
  decide +kernel

theorem k21_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).1 3).2 3).1
      118264237790600510285450120743928833373090613954543721714279632382319934328849223064878011896860536594816411456872).isSome = true := by
  decide +kernel

theorem k21_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).1 3).2 3).2
      350960336345699018635380716965556013140721889171255245811371371574614082514411419584906792774643489706326709608).isSome = true := by
  decide +kernel

theorem k21_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).2 3).1 3).1 1).1
      322777826342007271890948062249664599674364097345719615976213281868332098547997634398034626521313517471221498184).isSome = true := by
  decide +kernel

theorem k21_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).2 3).1 3).1 1).2
      369748677592022333243433822945384681526145464813351123957892248956629734784779763431629815288195888082032414344).isSome = true := by
  decide +kernel

theorem k21_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).2 3).1 3).2
      127905005091805568555313210959719350505204459761083023373504898154264421234129925413124519833478131826506010578568).isSome = true := by
  decide +kernel

theorem k21_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).2 3).2 3).1
      125431989751388001766704229821633172970966313811485791309596631901564842603029422888468196747970071538506413723272).isSome = true := by
  decide +kernel

theorem k21_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 21) 1).2 1).2 2).2 3).2 3).2
      332171994155645370737295177034610477307219018120093809307620085329745464823594881590385291087737023713042648712).isSome = true := by
  decide +kernel

theorem cover : Cover2 (chModeTFM 7) chCCellBox 21 22 :=
  (Cover2.one (box := chCCellBox) (n := 21)
      (.split 1 (.split 1 (.split 2 (.split 3 (.split 3 (.leaf _ k21_0) (.leaf _ k21_1)) (.leaf _ k21_2)) (.split 3 (.split 3 (.leaf _ k21_3) (.leaf _ k21_4)) (.leaf _ k21_5))) (.split 2 (.split 3 (.split 3 (.leaf _ k21_6) (.leaf _ k21_7)) (.split 3 (.leaf _ k21_8) (.leaf _ k21_9))) (.split 3 (.split 3 (.leaf _ k21_10) (.leaf _ k21_11)) (.split 3 (.leaf _ k21_12) (.leaf _ k21_13))))) (.split 1 (.split 2 (.split 3 (.split 3 (.leaf _ k21_14) (.leaf _ k21_15)) (.split 3 (.leaf _ k21_16) (.leaf _ k21_17))) (.split 3 (.split 3 (.leaf _ k21_18) (.leaf _ k21_19)) (.split 3 (.leaf _ k21_20) (.leaf _ k21_21)))) (.split 2 (.split 3 (.split 3 (.split 1 (.leaf _ k21_22) (.leaf _ k21_23)) (.leaf _ k21_24)) (.split 3 (.leaf _ k21_25) (.leaf _ k21_26))) (.split 3 (.split 3 (.split 1 (.leaf _ k21_27) (.leaf _ k21_28)) (.leaf _ k21_29)) (.split 3 (.leaf _ k21_30) (.leaf _ k21_31)))))))

end C4.Cert.Gen2_ChC030
