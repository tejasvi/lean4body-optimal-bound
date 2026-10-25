module

public import C4Check

public section

/-! Pieces of cell `11` of the chart root grid B: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChB002

theorem k11_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chBCellBox 11) 1).1 2).1
      99).isSome = true := by
  decide +kernel

theorem k11_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).1
      12674).isSome = true := by
  decide +kernel

theorem k11_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).1 2).1
      325605255033491742187070433443282493369102253123827951647590279104244820128123644556589189100306692909616693111718275).isSome = true := by
  decide +kernel

theorem k11_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).1 2).2 3).1
      218502499934257470096615384747277867884140911075430353988285619427641599155205454776374986832723927545500848563136334839324729579058061819112304319916850515866542149153002694584586339737133974961456617238104829596033126733119676751791646324384779).isSome = true := by
  decide +kernel

theorem k11_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).1 2).2 3).2 3).1
      343785731212620309657905699430489485160581323579511644382283901534962880223334599944252843271348613018173269242610642833425699067192899344906131797600862022311786023296955164173531855453520536682452494160109413147350973497041392082082).isSome = true := by
  decide +kernel

theorem k11_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).1 2).2 3).2 3).2
      182936054895154516449699530825295494752149577022188286250891042000083582749879216444083090844657534267504277425256).isSome = true := by
  decide +kernel

theorem k11_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).2 2).1
      1353966620688802971909444700500882033702727428756293463711114573795025683555798428723024912881328345640487646565633170072405379).isSome = true := by
  decide +kernel

theorem k11_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).2 2).2 3).1 1).1
      26673279031423586415307187791961605316365805977643712399090202251976263044633528817883359164552855718297594030898842626777159927384390550218525829733606531900571056783481840183583533456107047970060899535186791250702789666007745907317592706851).isSome = true := by
  decide +kernel

theorem k11_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).2 2).2 3).1 1).2
      426795714403588180413944312075834224288585546332938062700579376647033823104597145359475371616709126469310191318480609192177347429977005737737568318475591340246990122477064647365203936734825027829690989820725376884099250383021869048255368078347).isSome = true := by
  decide +kernel

theorem k11_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).2 2).2 3).2 1).1 3).1
      159053725372173455752627892823485345083144792943876358797336711719590687879758158592441418350409917539624747840584).isSome = true := by
  decide +kernel

theorem k11_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).2 2).2 3).2 1).1 3).2
      156752153639116374827768740265169902505036986531742803050433216144208562648982280950972687315702814067618682916776).isSome = true := by
  decide +kernel

theorem k11_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).2 2).2 3).2 1).2 3).1
      161533786339135672625793080436542181325739402815809250530686282563065993576142587408636601113664714405719062417320).isSome = true := by
  decide +kernel

theorem k11_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).1 2).2 3).2 1).2 2).2 3).2 1).2 3).2
      180585163768678788884458265317054854519283218433255343205414180149558592176662765640631035805353542058644151228648).isSome = true := by
  decide +kernel

theorem k11_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chBCellBox 11) 1).2 2).1
      207651075).isSome = true := by
  decide +kernel

theorem k11_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).1
      811630978).isSome = true := by
  decide +kernel

theorem k11_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).1 3).1
      0).isSome = true := by
  decide +kernel

theorem k11_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).1 3).2 1).1
      56524079312295153964549463005795200716560836401298914920308777026394372456590090119986882729814499733535963867263410192916418630202183798198305986403914907205815898856153948179890033836904608691450687167585178249465524850820214291932195).isSome = true := by
  decide +kernel

theorem k11_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).1 3).2 1).2
      3414194354504168524796295359849376848261592365671358307234638173293692914877247532104847077390179895312278711131354261055687572224919944221180947602014495475420015045575615178131279752269496304260078034470000141644158691766103939932901142401035).isSome = true := by
  decide +kernel

theorem k11_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).1 1).1 2).1
      645798994721082755745934471583016062106410974116854605452711161349630836738083193510401344109635890550630591882594608131).isSome = true := by
  decide +kernel

theorem k11_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).1 1).1 2).2
      318945442296319257056612336891749971915011899870740207295865046820641659161207765476693222304158611487127913039500273122202456805816505003817760025310489002010930704292164442499274605177476627101207161988456303355271120305566336090915).isSome = true := by
  decide +kernel

theorem k11_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).1 1).2 2).1
      2582486372022465282724939207478121934571357189363165694685815125648551833380306768188675789782429410763919864971415299075).isSome = true := by
  decide +kernel

theorem k11_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).1 1).2 2).2 3).1
      20175674849533247156621531602256471930467783844599917546479045068735898266611456833430363143672574515440580459522143848).isSome = true := by
  decide +kernel

theorem k11_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).1 1).2 2).2 3).2
      20175674689832348263324110047403207096400260478494999396836525682331026520542954329601243059610989089708018613139471880).isSome = true := by
  decide +kernel

theorem k11_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).2 1).1 3).1
      5045481916601146338505228899240801417763316392149138099894719171837595350878616060358510721716689126595136326374763752).isSome = true := by
  decide +kernel

theorem k11_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).2 1).1 3).2
      111458379886545705642343243959365200881484048722558259359509017944422999459520145163428217657615357924684724353010038725612336940949861055228025511882880809984314423440358023816305983707212200132828384845911057314246462695823843838761794).isSome = true := by
  decide +kernel

theorem k11_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).2 1).2 2).1
      28659484246094293176035630512401775454916872512867578375200598046893782714253269329904021100732283376491681936542714289137075291407880740268071542370987440874653071051787647482145240712931438338227064104538596459975723846671234721422019).isSome = true := by
  decide +kernel

theorem k11_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).1 2).2 3).2 1).2 2).2
      117817493930644126995320248110604334505598475380396896120144784928015386328319476898698542218333444697438436105987534328457046464001828066496725177765430154347768232361067111387488258134346933199095992194789351092868411538552805312537411).isSome = true := by
  decide +kernel

theorem k11_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).2 2).1 3).1
      3).isSome = true := by
  decide +kernel

theorem k11_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).2 2).1 3).2 1).1 2).1
      1291361434181464312774101835996478257502879626669593454420588789407281831654014353604979396123042245102824632948987302915).isSome = true := by
  decide +kernel

theorem k11_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).2 2).1 3).2 1).1 2).2
      53349001227772083544398044690334407324028110511896816811849245162955877904742615199541249742739698537305641374360096344828526417098951467771376757082565386690515349889659355820891539571076397785122479003766832369191333917608035501234136508451).isSome = true := by
  decide +kernel

theorem k11_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).2 2).1 3).2 1).2 2).1
      14176930433354576905205269551269068587045517628009253886266267020156383295150127358224979311575646395667713490551171).isSome = true := by
  decide +kernel

theorem k11_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).2 2).1 3).2 1).2 2).2 3).1
      20175674614678984104674929516364916898141167861240235517210563284554193389968322534165740937894338911114232685678679400).isSome = true := by
  decide +kernel

theorem k11_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).2 2).1 3).2 1).2 2).2 3).2
      20181217053784052061083931341146591745394586815549295235807785395252143544146032085360262005043875413774585363895062704).isSome = true := by
  decide +kernel

theorem k11_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).2 2).2 3).1 1).1 2).1
      2582486381942709103384692506452098651236972253201152690772956182677769676583534220583602782811806420612970365535399547907).isSome = true := by
  decide +kernel

theorem k11_34 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 11) 1).2 2).2 3).2 1).2 2).2 3).1 1).1 2).2 3).1
      40349501787232961849533566288574071752791903872992107678886452255890622700140150203438447232654531707719778753508450888).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChB002
