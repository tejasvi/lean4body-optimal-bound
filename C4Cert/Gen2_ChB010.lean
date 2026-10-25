module

public import C4Check

public section

/-! Pieces of cell `15` of the chart root grid B: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChB010

theorem k15_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).1
      3).isSome = true := by
  decide +kernel

theorem k15_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).1 2).1
      3).isSome = true := by
  decide +kernel

theorem k15_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).1 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k15_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 3).1
      674426326379226296181905930794976836062833097420830830211620851243999336110744666686334373868388470824502664667234).isSome = true := by
  decide +kernel

theorem k15_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k15_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 3).2 2).2 3).1
      103542550283091907367448014097030698467446539566230633626083561048280123491230752121525131504743987717902449927170).isSome = true := by
  decide +kernel

theorem k15_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 3).2 2).2 3).2
      523877845266369193619415625097106211740625367759613221647859980581992298979720067661210499571997028806757857270818080905701905713802374191293932496661406696956776455671184376559496353123503703604569113481331887184458408027312319628963).isSome = true := by
  decide +kernel

theorem k15_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).2 2).1
      3).isSome = true := by
  decide +kernel

theorem k15_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).2 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k15_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 3).1
      2851619402386372665199993320206772417390408399237410769408944403657893671330153472667850312021139549095240684699746).isSome = true := by
  decide +kernel

theorem k15_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 3).2 2).1
      3).isSome = true := by
  decide +kernel

theorem k15_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 3).2 2).2 3).1
      108352365623987745364060269836354326152086105908368383469581772677098224018116420966037056167824135987365256221698).isSome = true := by
  decide +kernel

theorem k15_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 3).2 2).2 3).2
      553375689267330733427751745278752197548194388363003248089568427660742751471300501680445670963539297851686281226233503378127835537584949885693921657734425342725807909711775806921494936220216353363880225319779354049935798577433363516579).isSome = true := by
  decide +kernel

theorem k15_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).1 2).1
      2183186745431840708533774185912345586480023873974500510600795869884398525560694838025186708526423096312079385056735797347).isSome = true := by
  decide +kernel

theorem k15_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).1 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k15_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).1 2).1
      10752741666366265465313714167239159814002289640282750267771687688155076557185295428791903822569951408172760621664910778423269680056287906228192698250715577741505812549135866698572931531923833231597127344234675733147845895785752960160867).isSome = true := by
  decide +kernel

theorem k15_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).1 2).2
      853544917877105731580418383278121317966153916166625888585678211256005357998882940328708272455803020873897317787277013992063568900643426167554046169237413096152349167599073971688094067256245279925984411604966006932496076897137877471370861655139).isSome = true := by
  decide +kernel

theorem k15_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 2).1
      11746353293534975377713735652969651808461520184158371940599865039412475234239519411854587570532015503065802241375057712024148581487431037604447938558146399567628603907105709039635747388317648173621580036182579391337749532673260355327075).isSome = true := by
  decide +kernel

theorem k15_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 2).2
      9759129633301532165964028327629667729971101503816275738204549629137129130568879628647529392144653036294715582879567022794027481213294826660057057367221519492622948610819039894239015709189063418686024395566955885127189738654838236333155).isSome = true := by
  decide +kernel

theorem k15_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).2 2).1
      2546315682076130507700421189531935380206872603493158780758773672269408561562346468733061370291436989629695571930534781027).isSome = true := by
  decide +kernel

theorem k15_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).2 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k15_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).2 2).2 3).2 1).1 2).1
      9884172510872875193877580308310775284100299896203976884043529533430069478327014092791136507032774649220192324026723).isSome = true := by
  decide +kernel

theorem k15_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).2 2).2 3).2 1).1 2).2
      10156574272621229949979943738985016456940090467285461599087818961056664609638070383955917070000244748397116764072739807968444999595511871997556457709292361737964927648009786692345098833254882182450785313811093554107525370082430880154723).isSome = true := by
  decide +kernel

theorem k15_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).2 2).2 3).2 1).2 2).1
      10807657107523201193962147691721395968283262541433444361721362497080445976918039023148990213726093509591072195740003).isSome = true := by
  decide +kernel

theorem k15_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).1 1).2 2).2 3).2 1).2 2).2
      10554018911369799150489142468527779779401216562654456075277028916712081527813438276923476950530732287897460637229522905148635724276915844534529332621388086461604266232172798284704933957156072314625168939562893801637257078225551702398051).isSome = true := by
  decide +kernel

theorem k15_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).1
      81645260483652794361402572007251474153932535715856606756552620950479656389951516361379146555830430316812222407581711).isSome = true := by
  decide +kernel

theorem k15_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).2 3).1
      304972813069119790354650090473249771762563780095070346158802034917427068639131415909366122769779143710002700668113925555522336105244634076835828948142973512670049440535209275823804195368647057696114864669242204496401940926914006322723).isSome = true := by
  decide +kernel

theorem k15_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).2 3).2
      135032831871769822850329248803772373565119237097185469662909201296731476242134283103340255374684658603858701725096).isSome = true := by
  decide +kernel

theorem k15_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).1 1).2 2).1
      1834207129381300565819903862135702353843412040913971841202047935857929106951073966516965828975137046587345536409121322864989380949843681892983575828795826014373385787800621001333058537589606383193205843787947111499825094380487590126170127).isSome = true := by
  decide +kernel

theorem k15_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).1 1).2 2).2 3).1
      323603031712630417999964777843967342474300356038834553142845424022479723343988709006817520164856789650773557088852034547770955194305920060608121477957663309133886875662974944455745991828828475528165816309864873198195970578990190924195).isSome = true := by
  decide +kernel

theorem k15_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).1 1).2 2).2 3).2
      135072757096674706104086928331724509228986723725081268344475616641930589793685826408629156940561065136701549588296).isSome = true := by
  decide +kernel

theorem k15_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).1 3).1
      137496453035904169915753616503894178239317644679848694735432459562881711331726918538097184636660658827023022766760).isSome = true := by
  decide +kernel

theorem k15_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).1 3).2 2).1
      745515524288400111398715025296816734221574833055289299737251858774553497103939306785500010170110257297462964168).isSome = true := by
  decide +kernel

theorem k15_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).1 3).2 2).2
      538843768079294555681428270085604408805864455601264260550101189326063051985329229224696803324330859133952730024).isSome = true := by
  decide +kernel

theorem k15_34 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).2 3).1 2).1
      180829412222703736138311511254537147471037564052933977608585714719238712436897247614865404438417092878832434297512).isSome = true := by
  decide +kernel

theorem k15_35 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).2 3).1 2).2
      229042642897267670845136301935871556690121010983930345294679473449285913026949861052552263438653915038595590378088).isSome = true := by
  decide +kernel

theorem k15_36 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).2 3).2 3).1 2).1
      642179640801194175917213451787510404353191220468725806748986123699515416873322271954863585244574537611303792584).isSome = true := by
  decide +kernel

theorem k15_37 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).2 3).2 3).1 2).2
      202501763166605082746409762197739921437682603978807127495914779794831541824611761396431745230066976043021989919336).isSome = true := by
  decide +kernel

theorem k15_38 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).2 3).2 3).2 2).1
      154582100311696951791046445287426784321653485867042780426092804638597957417229393960311864961353259640728755372584).isSome = true := by
  decide +kernel

theorem k15_39 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 15) 1).1 2).2 3).2 1).1 2).1 3).2 3).2 3).2 3).2 2).2
      197729524636797743467895399386788584378784726522749010536404044742764590613277691636053403230846752179146331367656).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChB010
