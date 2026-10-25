module

public import C4Check

public section

/-! Pieces of cell `1` of the chart root grid A: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChA000

theorem k1_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chACellBox 1) 1).1 2).1
      181713841730752312672080628528753729837543318140259179904136126153917475672154843040278117877344631634370372078663406957748348646375683).isSome = true := by
  decide +kernel

theorem k1_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).1 2).1
      0).isSome = true := by
  decide +kernel

theorem k1_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).1 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k1_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).1 2).2 3).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k1_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).1 2).2 3).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k1_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).1 2).2 3).2 3).2 2).2 1).1
      5164501726104180602823359841486827980680845317739917926041405042190351526501232356850386933193978887708142573683765174056).isSome = true := by
  decide +kernel

theorem k1_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).1 2).2 3).2 3).2 2).2 1).2
      1322233034172973034624511211389419717447323888607819622239986930150888598550943893368123060358106722783443598705486361002243).isSome = true := by
  decide +kernel

theorem k1_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).1 3).1
      49538).isSome = true := by
  decide +kernel

theorem k1_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).1 3).2 1).1 2).1
      5164736240790356362152283368990779728125451308965006955433050164642780834684586019623201521148269540274091698676101723139).isSome = true := by
  decide +kernel

theorem k1_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).1 3).2 1).1 2).2 3).1
      20175891138562402672273356727670870586921384616317683970617328219297794472857574380230673044150126296236118708581616840).isSome = true := by
  decide +kernel

theorem k1_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).1 3).2 1).1 2).2 3).2
      221694053136834752521112706444542000186712850148663139297456213767070923009912479536975091250822911543115571529704).isSome = true := by
  decide +kernel

theorem k1_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).1 3).2 1).2 2).1
      13337397907943092057665460191459519202740634716784983166715437659308443666426540107563157236152974928622425015897446177861666471140950183194685182087939416593416062779620751714285946833121425948275048310424971219761898105955400595444081382179).isSome = true := by
  decide +kernel

theorem k1_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).1 3).2 1).2 2).2 3).1
      20175893336798259943799908649399446566642261634094235846412472221134975356348305986940239110063980786289261113498871592).isSome = true := by
  decide +kernel

theorem k1_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).1 3).2 1).2 2).2 3).2
      80703390019959020422294297934247234485265536294035149336902247398761896343591957019512259189520410042372605999702693936).isSome = true := by
  decide +kernel

theorem k1_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).1 1).1 2).1
      13337394858797560991699345249262297515379616659770651866640034096696921617519671764972395941945514654747273970344841945060866021942947629246572505999322879593566812201176377169969087387727012975529877279768263817247241396653908495860931723171).isSome = true := by
  decide +kernel

theorem k1_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).1 1).1 2).2 3).1
      53363659316861143227169070616197053517682275196631248273621179687569381445502472304550114475981263077692317300409329508724937048643226985409682736232924199132209629293432034148635670773929477687774307122941874466270814459578721214314636661155).isSome = true := by
  decide +kernel

theorem k1_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).1 1).1 2).2 3).2
      80703544638608511829958891753541132302314164560007137207644160786853830150058793636212906460598390191463001331786847536).isSome = true := by
  decide +kernel

theorem k1_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).1 1).2 2).1 3).1
      645564316961503620362164543870244033708227474032448586943585585862118638267555700451794104990354540444035111642496992424).isSome = true := by
  decide +kernel

theorem k1_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).1 1).2 2).1 3).2
      106707775177344585288394413192217026237505727183275959472456515496332341344504141229904836605497957369804136318736024999608009471556472560603720460804075444483147177032704304519736858440238621825110116718215839463510218295069762740469568930211).isSome = true := by
  decide +kernel

theorem k1_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).1 1).2 2).2 3).1
      853584024413689097963789708434533091472299197692163729165373435326650614764231068690206832917642567719359841872745843987678235139648212209705217584301534698411232614460805945179083285100574626643081950997547860871597549971810296492805650145987).isSome = true := by
  decide +kernel

theorem k1_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).1 1).2 2).2 3).2
      141664172212250826952810636705474517707727093414814406033536799292124207336753196164435256320720257675048502703645374577084553364764182587195585006273352576598150923623074474859975546498742046610260103910125179264800714227024782225875779).isSome = true := by
  decide +kernel

theorem k1_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).2 1).1 2).1 3).1
      10088981958151300510736272840329059294339301465945554956056919516756499084802316324025390226704617312292070324555737480).isSome = true := by
  decide +kernel

theorem k1_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).2 1).1 2).1 3).2
      760978877641123608076108947347917145183480448085259502943037353861074409746272960649590505653988784936918259168176).isSome = true := by
  decide +kernel

theorem k1_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).2 1).1 2).2 3).1
      144843728990342824885185859116531313847825982729911075425392347286575412401626314315258273112374508372052259315000092000280071597992813773380785869451451742097341671781596103091122783461289290036271415769033443018882127379012059734489922).isSome = true := by
  decide +kernel

theorem k1_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).2 1).1 2).2 3).2
      33884772682219095896898274525667224019097439384870070616054340533646338647797164767702859470230001785604413090584).isSome = true := by
  decide +kernel

theorem k1_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).2 1).2 2).1 3).1
      80703332151869785760541465217316946726240105931156501678832579126833536425038752389724562635941516304191145384591169712).isSome = true := by
  decide +kernel

theorem k1_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).2 1).2 2).1 3).2
      13580579003601042177513902971537514480742172428716108814224076450335419034300128129638615433966946302577666573110040).isSome = true := by
  decide +kernel

theorem k1_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).2 1).2 2).2 3).1
      13428468597668372498722680854218846358802376016119906861242456221454516140010028707980025495583522656126391517889304).isSome = true := by
  decide +kernel

theorem k1_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).1 2).2 3).2 1).2 2).2 3).2
      20056553940406536550242854063156700466576589376892781540153011103720086842985729625697440629720009657225320207128).isSome = true := by
  decide +kernel

theorem k1_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).2 2).1 3).1
      21663466082324552895037586519948997839976976765314605328343508060543809303941216924783898281590097921385732953634096826531479938).isSome = true := by
  decide +kernel

theorem k1_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).2 2).1 3).2 1).1 2).1 3).1
      5164736252514281151739598507905555938241609878761250637062373061690578716653013242566754142641265101330067631048940315650).isSome = true := by
  decide +kernel

theorem k1_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).2 2).1 3).2 1).1 2).1 3).2
      3414336057910292453668031970737653371920027973553775889547680373057684460659977879176817624927268875505002276834379978955417052877638132460233710333931214857062657850702865345042243582273322684989780855894293067267340395231382314651360655117122).isSome = true := by
  decide +kernel

theorem k1_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).2 2).1 3).2 1).1 2).2 3).1
      3414336056320514080879678114698280211744359204773065941256290264065532424631665655531919764092726353564620960869126533809341781209204045744992755550929916546131622983315032594575315512856038607955181727012046664115017745139957239030251257709379).isSome = true := by
  decide +kernel

theorem k1_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).2 2).1 3).2 1).1 2).2 3).2
      103509487178941468205151011784269424554101186018430790826988761447911043665152022439197540684067670016263688569849453167786223074449149284064072556107851441622205482401339133732346624468115446794241442140768786012376070774363607243610946).isSome = true := by
  decide +kernel

theorem k1_34 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 1) 1).1 2).2 3).2 1).2 2).1 3).2 1).2 2).1 3).1
      165294266653509176219573637863659500276621297274676574800922674792494182645829496336411733644503246288245244061574542524802).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChA000
