module

public import C4Check

public section

/-! Pieces of cell `8` of the direct root grid: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_Dir007

theorem k8_0 : (checkBoxH2 dirModeTFM depth (splitBox (dir2CellBox 8) 1).1
      3169).isSome = true := by
  decide +kernel

theorem k8_1 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).1
      1).isSome = true := by
  decide +kernel

theorem k8_2 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).1 3).1
      3).isSome = true := by
  decide +kernel

theorem k8_3 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).1 3).2 1).1
      110646855154296640953154929962985185008748468488655392534926161409867656174018815387758963886955017483813082367075).isSome = true := by
  decide +kernel

theorem k8_4 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).1 3).2 1).2 2).1 3).1
      110649007548993559272314689151276884792973749029731218216184216342481129433846468997453224614249534843465994863631).isSome = true := by
  decide +kernel

theorem k8_5 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).1 3).2 1).2 2).1 3).2
      385703960640980198778291697671706679376201200907070559089668868512344356742085457913647874687654347505988659859893780484426949177062786744958303434145406673747692501205574441951067848433589948852297849882404642452788696018930882445347).isSome = true := by
  decide +kernel

theorem k8_6 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).1 3).2 1).2 2).2 3).1
      2285991875560979177122230909769321031110783818876009242542606157958253650695569084769941400536954673896266818210799195081960543261884795383240188663860998148963518673684596723572552149096474651734162160966800043056040387845135798012941).isSome = true := by
  decide +kernel

theorem k8_7 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).1 3).2 1).2 2).2 3).2
      236662289198282529138752647060741004772077390328116394696999588062841221834594056672047751695002849929912901060808801877490143944155642695181436366450462638140382171373381811801235312202596210796415705939462188169411062877523526156323).isSome = true := by
  decide +kernel

theorem k8_8 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k8_9 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).1
      73157531313927215255688635003197980836582500505498053888274406853321553689643240216760828803807321610683067688151003620578249379940157321634707703525620297604011484329616854318936377123799710992969168876947200698870103656490922960520291).isSome = true := by
  decide +kernel

theorem k8_10 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).1 3).1 1).1
      3).isSome = true := by
  decide +kernel

theorem k8_11 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).1 3).1 1).2 2).1
      2232664664166218854576919645613642784203061498116376477343020538140930349472918869713672420707189164387511664254420912377982834137242163049956433968169719933605736560890065271821510427594687959277887830834681492842828419704381517475).isSome = true := by
  decide +kernel

theorem k8_12 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).1 3).1 1).2 2).2
      330529875694880605750376282677852643626186496305461960157494342120421675058060777362235532488164882392729018112010804043791).isSome = true := by
  decide +kernel

theorem k8_13 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).1 3).2 3).1
      2232291959434193042382518865756345469804177433924906135688406157676037353673788167871738373077343978682173332280560223132903489358453631462406702503939689052898315937489011831595175555311359272830239449202715684661938744903005646753).isSome = true := by
  decide +kernel

theorem k8_14 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).1 3).2 3).2
      179517339044572959160230907140445698022372482655960238141466993757258133652318890097207440156487841183459204392).isSome = true := by
  decide +kernel

theorem k8_15 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).1
      2286812851910355461177266532556521174549826002585966941155695981892417927221917633545201564707939016750904435370048311850467004980002170883316004218832654100281169024036954664966723454205686094551146148167358175830096401795926499296291).isSome = true := by
  decide +kernel

theorem k8_16 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).2 1).1 3).1
      2233027388426275982299413193725964547198323958085829035219583717451805925056987430044722026184862007450818705924788922618987828509061296916871675577007708436702290618698447494972845446308722861905918718187906519856784291252760732193).isSome = true := by
  decide +kernel

theorem k8_17 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).2 1).1 3).2
      3377096027681098084211870826213412435503669776732304123501140860772865835733824858013021373452302458138150792).isSome = true := by
  decide +kernel

theorem k8_18 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).2 1).2
      2232184675595769382729511348302857651994136811961594290194982972601576522547497364001397935686928667835170320223647390046584137200259028959757667431881220534515786471942829451438229968108527044867584258925633884512634461448571584547).isSome = true := by
  decide +kernel

theorem k8_19 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).1 3).1
      0).isSome = true := by
  decide +kernel

theorem k8_20 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).1 3).2 2).1 1).1
      108072186354275219463552752835151252704879272035681756628084235046174326344792308917757061719345263322926258435).isSome = true := by
  decide +kernel

theorem k8_21 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).1 3).2 2).1 1).2
      2232327479339539827341643867139096048007201239461006337624168182148534560561985379892791312583456928155195301080898176522245651899389397724269448697077784421164577382243084570026492684556351180541562984513124215062665168244904535843).isSome = true := by
  decide +kernel

theorem k8_22 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).1 3).2 2).2 1).1
      99).isSome = true := by
  decide +kernel

theorem k8_23 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).1 3).2 2).2 1).2 2).1
      2232504912181731002952599810703887388130928190143947034444912326383144359330147505499757580565529116813950754261473074003944793524739010097876617767693677214215468426594777430636198565868403141089868969661797872255966415025514547107).isSome = true := by
  decide +kernel

theorem k8_24 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).1 3).2 2).2 1).2 2).2
      20658058127812641162867656095631907731796941632356305593161803988036972533366940617437969117551284173772497107288283898115).isSome = true := by
  decide +kernel

theorem k8_25 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).1 3).1
      180341196598728729139015164998595418391968049611211158504225665950455912448750231440633438921954200428752567036146545803920321194442634384541209534865240222185366350911919186528039650480565045332810140509358021462393126857301043456147875).isSome = true := by
  decide +kernel

theorem k8_26 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).1 3).2 3).1
      213377682804295856572585787052849411841364820315071622971555987337996802032828951659193430681160209992164991848460819807184681220335371215439838301653535879873732267526295449302528679035676328074492826342101971320853136044005908578311025732513).isSome = true := by
  decide +kernel

theorem k8_27 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).1 3).2 3).2
      200654102842476706380627966470737410091165440917022447424191645989950305293124570635830206434869477990520455176).isSome = true := by
  decide +kernel

theorem k8_28 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).2 3).1
      1).isSome = true := by
  decide +kernel

theorem k8_29 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).2 3).2 3).1 1).1
      2232524695145059032868247737515337364291733168916479733682800273421352455283888153428049033576592627870182292155022749209352336376874272536961882967894020736619706640635157393275716593911512260342549286176901928076474578690560687649).isSome = true := by
  decide +kernel

theorem k8_30 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).2 3).2 3).1 1).2
      3376823258650714162243464788263788725181209089576420486047942866931201045247873229040522169817733706974149864).isSome = true := by
  decide +kernel

theorem k8_31 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).2 3).2 3).2
      285201756765953414390816372348528496068846525918062189517803287465203669702227127026012312577024658081559941320).isSome = true := by
  decide +kernel

theorem k8_32 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).2 1).1 2).1 3).1
      255292485299113027243128372824651739590624640703753895599661722562150820839455011821460807952260094936096667587014698691301739086448747986669099610532673760427470084487942409096631269253636195969175165813214527972054285242515439541923).isSome = true := by
  decide +kernel

theorem k8_33 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).2 1).1 2).1 3).2
      249082279313519714830063871362599462219799528911072863614057241424167855063682335846907146876740593611546154652231852959712580836720509791962219075384709221083165643748474742276689922119357715728535387290624597122820045881702706850979).isSome = true := by
  decide +kernel

theorem k8_34 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).2 1).1 2).2 3).1 3).1
      2232221011392634198999288027366829761819640797439486014921782083260356686564917220793408960318468649703614342233248112686677661127384390734665488388648227952747206826021465920474737268690578606088382445885118912442594421925883368865).isSome = true := by
  decide +kernel

theorem k8_35 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).2 1).1 2).2 3).1 3).2
      191259993209502825053718299752407492783886792281758488447435928396629682451597886714013837371801235270104977608).isSome = true := by
  decide +kernel

theorem k8_36 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).2 1).1 2).2 3).2
      261502449900192927270768813600110547048263063767380228173905626799241752932051340892978914905585169333082562216096656822712277800379555452839390074079486187723033792102117113773122682240843773726524568072047423306911158231329151397027).isSome = true := by
  decide +kernel

theorem k8_37 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).2 1).2 2).1 3).1
      261502438521811436477726745433438463683543303300041552571284671420581554013564250333281860348937079440377682487591174596296599472199551941683813034798461430885313252508066200587745375287930215067109202486382476877463036423754260938787).isSome = true := by
  decide +kernel

theorem k8_38 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 8) 1).2 2).1 3).2 1).2 2).1 3).2 1).2 2).1 3).2
      1142706690389237829487702783641086607689387601070637004066391321937580487684029155032619448603302566811355498580648477842461081266977207166763416911572155549348379768223423251851300361492019714665172016612062955848007738125261296424056).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_Dir007
