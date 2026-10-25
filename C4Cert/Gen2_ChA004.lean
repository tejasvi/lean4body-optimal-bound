module

public import C4Check

public section

/-! Pieces of cell `2` of the chart root grid A: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChA004

theorem k2_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).1
      67998111650007272583677879764672887171453050891873701718885536842233214863683919894894038789085673282253916636347187985694422026298534110278124844540922545317173392360394374558869816331).isSome = true := by
  decide +kernel

theorem k2_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).1 1).1 2).1
      2582514961564069872619887233605244521373577840018464862036663902694033479114405249375126737173248635671435747167939544067).isSome = true := by
  decide +kernel

theorem k2_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).1 1).1 2).2 3).1
      161398007449545269120108307938846531215120908599903931660239871632629038307786190647423237687333211562495028250506315696).isSome = true := by
  decide +kernel

theorem k2_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).1 1).1 2).2 3).2
      10088926682853069192670445244406190521189242626646199858709130192612705109369602180549871257103024970385948931831552456).isSome = true := by
  decide +kernel

theorem k2_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).1 1).2 2).1
      10329945608335238166574979380776453114041712556495014088798719823924460952650658771794722849904303183010315000518315266179).isSome = true := by
  decide +kernel

theorem k2_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).1 1).2 2).2 3).1
      40349658047513699422435654445563806576759614227768121833397464515508092659578036788697115207308945500149753045354250728).isSome = true := by
  decide +kernel

theorem k2_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).1 1).2 2).2 3).2
      20175900523338559481893271756950573941513955192785203019721953297206373147495543079198184609585823818698705113807028104).isSome = true := by
  decide +kernel

theorem k2_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).2 1).1 2).1
      106691893778034509192654461606958038083326184868306966506245276159512993346968286580712247637711134376566759285567090958013704134625953264237278185700403805738920987081196318098598784378785381370919545057677424482125410242354817466891079778339).isSome = true := by
  decide +kernel

theorem k2_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).2 1).1 2).2 3).1
      125321608249723678445690677464317470290456939158126994785759459919766356286562085437476030658859863094294676078600).isSome = true := by
  decide +kernel

theorem k2_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).2 1).1 2).2 3).2
      322803400422599794691313385206921574617153326425191266108954055842557672248638402541995135350100537564967048666234091312).isSome = true := by
  decide +kernel

theorem k2_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).1 2).2 3).2 1).2
      8550649012705727827153064414234709759129559813331766751503720705114129821527947944497915065658003917107615622830229).isSome = true := by
  decide +kernel

theorem k2_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).1 1).2
      6312940224036524746395462140810062006980062527513261558269796090806355386583886316300797698468497436720924182057616421).isSome = true := by
  decide +kernel

theorem k2_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).1 3).2
      16209601684683760648017854821918081717541083056488552105273003179983827490346453365331473863919465828198330710297344194244612760566303128163554382374321515853140797487980066723157).isSome = true := by
  decide +kernel

theorem k2_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).1 1).1 2).1 3).1
      154074815092569483229832237396841461647630872486041707952296208956931698085354353855848776442763862085866416941448).isSome = true := by
  decide +kernel

theorem k2_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).1 1).1 2).1 3).2
      439474403831126997953654471540990944664957262389603533372479846385578383997185930340993426150322937893503935214787364116926277581743657536508923152327859416652016534888579690128046299215502622109278640747239873337832594288285634052647745).isSome = true := by
  decide +kernel

theorem k2_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).1 1).1 2).2 3).1
      113048158140759090102007275462305018435432052143385073384814923999486282146877894709404798085581829262607211128849152682636733509653513522886395668767600445833407635480792270627727597450017873999927492283283482931379987267242981211784001).isSome = true := by
  decide +kernel

theorem k2_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).1 1).1 2).2 3).2
      32682318781250754053753487127038771983763387090141578878241810083848460641619963594013240563610703823792066435864).isSome = true := by
  decide +kernel

theorem k2_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).1 1).2 2).1 3).1
      148023285777827357419709424912485462078820816027242004985794594708675719693599621794422382107627793678997087621779043456808921986967894063203143405241540390964190961849507600506042048322914790246014688641290066653290016055906162959117122).isSome = true := by
  decide +kernel

theorem k2_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).1 1).2 2).1 3).2
      76483251889553650726350692927755070171972760608777032984771971568109329244313780393408160063415559438431587737736084765600014592424394639814223175893472136620065657114317626909610926435625112244264218632392855096406166582183544410123585).isSome = true := by
  decide +kernel

theorem k2_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).1 1).2 2).2 3).1
      13580579003544151786128477960104224654732564374306313911330837506275789029664687770113136760410291503014478622206744).isSome = true := by
  decide +kernel

theorem k2_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).1 1).2 2).2 3).2
      20657780748349764891234990567297363491271784947415166818176283644607842798870799839607858874353794633763859483416).isSome = true := by
  decide +kernel

theorem k2_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).2 1).1 2).1 3).1
      33884772544960363825780653050077327088039285065171280353346917644447930706957073624523529785483611087223329084184).isSome = true := by
  decide +kernel

theorem k2_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).2 1).1 2).1 3).2
      122914352101017363724467937996503911566048900341278650513670622438213379009696703131930457562922542821052247506952).isSome = true := by
  decide +kernel

theorem k2_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).2 1).1 2).2
      11707907512894902193226255069359085701101332495043444024218554484180187707885080403712947109616073888521201915523864).isSome = true := by
  decide +kernel

theorem k2_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).2 1).2 3).1 1).1
      11413156024624696919448424700633655770680799024960093152814811310287558898738558558400234379110356457219808264944408).isSome = true := by
  decide +kernel

theorem k2_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).2 1).2 3).1 1).2
      161396278703055948353239247981036177247645067009370530881787312852385135743340467903314152548390709188955776812554083304).isSome = true := by
  decide +kernel

theorem k2_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).1 3).2 1).2 3).2
      80700986868330170583986439268126165855194140702933038654659690140844038398372598345800763091953281125827222126539210632).isSome = true := by
  decide +kernel

theorem k2_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).2 3).1 1).1 3).1
      1325477855341895739177134669968604631719745185389885951875465687701171117234488953078636295511275514106630435221194298726027682810621047107469905417089383006334366385464410728106483603795231906965435128374133223329239774221002650280414306).isSome = true := by
  decide +kernel

theorem k2_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).2 3).1 1).1 3).2
      8171490880144989331032184580640751117744790518145616808552521521449352407346970408380355627485614879339482165885720).isSome = true := by
  decide +kernel

theorem k2_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).2 3).1 1).2 2).1 3).1
      38093360925531589945742826542852842895682911480205467087456257819830422655780899128641013235720488315060084611864).isSome = true := by
  decide +kernel

theorem k2_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 2) 1).1 2).2 3).1 1).1 2).2 3).1 1).2 2).1 3).2
      35688453244274277855278133170730333659611398625076648869396953354545139261371799130450642454948996951349763949336).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChA004
