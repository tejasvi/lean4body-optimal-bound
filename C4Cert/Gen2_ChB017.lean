module

public import C4Check

public section

/-! Pieces of cell `16` of the chart root grid B: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChB017

theorem k16_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).1 3).1
      99).isSome = true := by
  decide +kernel

theorem k16_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).1 3).2 1).1 2).1
      1291361464242810742827969853844896303467252683964966904222372215529922724883797600945711810931050905254828896544394892291).isSome = true := by
  decide +kernel

theorem k16_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).1 3).2 1).1 2).2 3).1
      80697291002095817396013985358349639877159694742504469880536518291534573041625403001915528144392623328616680374789170504).isSome = true := by
  decide +kernel

theorem k16_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).1 3).2 1).1 2).2 3).2
      745515501829846362008842626584006589787998522744427891916974801941669368002851693898481725052160317405388291400).isSome = true := by
  decide +kernel

theorem k16_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).1 3).2 1).2 2).1
      2582486369617558515051633712361839342600743887122175591793644324661157608895589687010945940700316295836083289162989167619).isSome = true := by
  decide +kernel

theorem k16_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).1 3).2 1).2 2).2 3).1
      683787199691177766045823590701832475014225654518691016303456309779466895350513869692970039063056991931779675551331812038320310390963520441536340561414481436865133195434870770119969036327183373582694718538123258492687758856358625387427).isSome = true := by
  decide +kernel

theorem k16_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).1 3).2 1).2 2).2 3).2
      20175674624073161481109905726392114408667875543588896406100046889609058091995177836145313899666285327393899141731619336).isSome = true := by
  decide +kernel

theorem k16_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).1 2).1
      161392465224157605824958219268334800527367189938295737749249927087180206856209009859580877554361876543252962944783494472).isSome = true := by
  decide +kernel

theorem k16_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).1 2).2 3).1
      640316700508295176129148174985231872832742249820413275437551026925772240873707579544756228528415885204872594501025318765376431069658973010600929970110822201520262093526433541516217113087739173332037857768923583013104300986373361188641).isSome = true := by
  decide +kernel

theorem k16_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).1 2).2 3).2 1).1
      783148363442505403479078041752945437434804152970759647341006792646141094119904207909150620610539562763933554397787799674596440977195164230025659027095999526642198469461806298087414921370869452689207063531528688013297285545908807256993).isSome = true := by
  decide +kernel

theorem k16_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).1 2).2 3).2 1).2
      3649048148414347905585136594116516771088691504388058799135894068202198887023141732847914250859168833966335009712).isSome = true := by
  decide +kernel

theorem k16_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).2 3).1 2).1
      80697156684248433608584685105946341746365395565112012461139207089709525056564002528350362684589960915574800714400626120).isSome = true := by
  decide +kernel

theorem k16_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).2 3).1 2).2 1).1
      1668225167394663539866523302746484576403392128100938278855219329237137100423685198657408050325250331967948050401440668716849121023553367358007596260026049272502127470566391505591909800943377937190699808976070651456174665656194755134956848417).isSome = true := by
  decide +kernel

theorem k16_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).2 3).1 2).2 1).2
      1262878149730227406743783503486853447354150916053959490448668212135268171004289454976263750564734792569943026641220360).isSome = true := by
  decide +kernel

theorem k16_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).2 3).2 2).1
      53383212908077266997590494647608444086557034008020542928972274819163445057909468275688208767864021204664972674209536074730480571429208457245368834854561832135716084946504802950018943629066236054500276342254253768859294589099882682258948271777).isSome = true := by
  decide +kernel

theorem k16_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).2 3).2 2).2 2).1
      739677854942410035533575622786845431384039747162208593755050812993286033739905018937829846316892372553178826457212883527121723403600392148661280789910673069806777337148219751432991634153426620995114934861492599164935321106030755648289).isSome = true := by
  decide +kernel

theorem k16_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).1 3).2 3).2 2).2 2).2
      14633769193766966274670438028407036656702046469412414051496039028582204608367688881633702486143048226498733970640).isSome = true := by
  decide +kernel

theorem k16_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).2 3).1 3).1 2).1
      6669236159726508610304167647152588014541375775815734980494739672804199351748323319397097197780857509843606612318043537047779268148906133381753952927282344552554794934605695875145332261803060950016538963809659782978137554435970699720427593249).isSome = true := by
  decide +kernel

theorem k16_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).2 3).1 3).1 2).2
      153190068898295526861496259944513522462213220886324860325136911991547326442550198724359862236666929437181492717908016592364408866043447067053747788464642095970792737948170623042565602444516459080086930761788567513488143587640663393129281).isSome = true := by
  decide +kernel

theorem k16_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).2 3).1 3).2 2).1
      6669235985844480976650872763655140354647569070698034124506070779782428118132235677622497614471793987750884047053061337819280811460175035651694795544241768559449943238795703969916863265260551963669500589623150349968267966031017787982761524897).isSome = true := by
  decide +kernel

theorem k16_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).2 3).1 3).2 2).2
      152792624000818480013728786967883744621953351011366918140285381485424545804728672349184803461069775592325817308217196552443885456427907452219933762091808352243895104898152116855774809949462228010511526512526887759952982439356799043894081).isSome = true := by
  decide +kernel

theorem k16_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).2 3).2 1).1 2).1
      10088761347803802304334951547902020175376218368120458903492924289917391308680095427502565749610260303063645208311858728).isSome = true := by
  decide +kernel

theorem k16_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).2 3).2 1).1 2).2
      3282675468999149378430642773862615768028393693984095562935661837020611127723322734248648043012915989109033617456).isSome = true := by
  decide +kernel

theorem k16_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).2 3).2 1).2 2).1
      10088939346194693054894422644195348901463278886771284491195697936415872403807754030726830792004991953915517311744841672).isSome = true := by
  decide +kernel

theorem k16_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).1 3).2 3).2 1).2 2).2
      13130701870967014469302462549491992519027026569796052700759986309870535663213371468252145768577027155412706671824).isSome = true := by
  decide +kernel

theorem k16_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).2 1).1 2).1 3).1
      404333941647647252681345519357623399955025884257572665117759637049240342051996490125555422803955328475574944602928967688715763484594342759251526830795451564566228405873429707598741899847497422013450684974403535002626022428960049168547).isSome = true := by
  decide +kernel

theorem k16_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).2 1).1 2).1 3).2
      207133089131400086148187758930985170775722527410997326462167315220977720094887931110848329744153898034117012020872).isSome = true := by
  decide +kernel

theorem k16_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).2 1).1 2).2 3).1
      132125502124910590793564009669225946439303137402835270086278693092160125606741273095670313554433959364255689011552307099600910755319098267795047093873134633419560608116854868521023565533539525034981395649254409012056807031378292142304067).isSome = true := by
  decide +kernel

theorem k16_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).2 1).1 2).2 3).2
      226231437412552473400461901179116713194826178183370067602077452512929357737442269474830020471819319973875998179784).isSome = true := by
  decide +kernel

theorem k16_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).2 1).2 2).1 3).1
      1716696923491852833609613184149997921923096105821882096027404529004530961705664937223169828452952563121156435477792499010470528927230172320384871036933633736724593681047666751904191673337938856872412565894662381921343171586264334840515).isSome = true := by
  decide +kernel

theorem k16_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 16) 1).1 2).1 3).1 1).1 2).2 3).2 1).2 2).1 3).2
      207180059982636499243989876838025302098076468557826502644761765491947979570957902102018879110720641205566140835624).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChB017
