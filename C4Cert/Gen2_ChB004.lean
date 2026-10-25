module

public import C4Check

public section

/-! Pieces of cell `12` of the chart root grid B: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChB004

theorem k12_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).1 1).1 2).1
      3).isSome = true := by
  decide +kernel

theorem k12_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).1 1).1 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k12_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).1 1).1 2).2 3).2
      14882003728104409672068577496283851012010482405311322837579409406300559435105977210669444632288513475169845814059788881795422125833091116755670959902134899637033904018403989137041927667076653963118251588936846056343775883634853165572886539).isSome = true := by
  decide +kernel

theorem k12_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).1 1).2 2).1
      49539).isSome = true := by
  decide +kernel

theorem k12_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).1 1).2 2).2 3).1
      11098648687909111997690642466994288402726172439934631091923531872502218363187601986872449982970519829132592876224771).isSome = true := by
  decide +kernel

theorem k12_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).1 1).2 2).2 3).2 1).1
      387256234155824336385733739197799611626160190872454923809085585594909291839441691931067638705049128456946993813624078988824729640147379547943280643269472024769359983556555918127516994165663395139400117862938423448547999715922644787235).isSome = true := by
  decide +kernel

theorem k12_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).1 1).2 2).2 3).2 1).2 3).1
      576420424544751166713167283828644154931468216308410181528432150217690962850199394861076695035077831931439855016).isSome = true := by
  decide +kernel

theorem k12_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).1 1).2 2).2 3).2 1).2 3).2
      228852410926598337001580272264962564339235108433652490982131717355054908393064136735642470991976743777812459981032).isSome = true := by
  decide +kernel

theorem k12_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).1 2).1 3).1
      3414194555611151819020523377119999065801333041659582576300426010904434300956050038083706107787028007315167862322287688206610672638784314092136374071656964863223299939578195219325872078068493176873565863783863297636533447887068678575817177223181).isSome = true := by
  decide +kernel

theorem k12_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).1 2).1 3).2 1).1
      482478719416124133563211491399605933662515422905264441377603517579068936490729962560506278749407340288708355848).isSome = true := by
  decide +kernel

theorem k12_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).1 2).1 3).2 1).2
      40349501909357165674654669261138112418222683956533167511438864729331367233684499333591962847567753035077188123368569384).isSome = true := by
  decide +kernel

theorem k12_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).1 2).2 3).1 1).1
      548237912612246036647575115625543922665681061816207990636218198029182708328815745506990124297081579650853084648).isSome = true := by
  decide +kernel

theorem k12_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).1 2).2 3).1 1).2
      171087657560302847377385490864469235655344452346180556357923600901103974795837020096199851625711297154587415686504).isSome = true := by
  decide +kernel

theorem k12_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).1 2).2 3).2
      331365581526632549414182083523968161856967449277259332707929767503515960025498092777341437905204242086805765883597775322690348720224016423127588641391239243446029807350186683584215550123701905568878711494867116366145051477945026115489).isSome = true := by
  decide +kernel

theorem k12_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).1 3).1 1).1
      834723147484651967751593868514731294211168792245582465039708194026397475034315304528886863736161194967490756873026763736946027553550733071938720475129870055806567114590504612472169003121655389101985511946849889057258062284056148120428203810).isSome = true := by
  decide +kernel

theorem k12_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).1 3).1 1).2
      13056937979504800603849407729252204197757723722776629746983665903868285675152824802373131898154920194257138513468699992990886123211716960732869133570346308914967844847625781372315096867425223179594336414131783645881257779847050420257247246).isSome = true := by
  decide +kernel

theorem k12_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).1 3).2 1).1
      178368139565639550011937870979965582720695376038202390878614557955869350478073922195224525669782331103275716302184).isSome = true := by
  decide +kernel

theorem k12_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).1 3).2 1).2 2).1
      40349501655714566058126580913431307638469468667356745763073560084252541242092395793838077424827839058257833404596512360).isSome = true := by
  decide +kernel

theorem k12_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).1 3).2 1).2 2).2
      567026251120131440879403862049120589001068642889907439535854573855780533019976503574021798409424619602623334344).isSome = true := by
  decide +kernel

theorem k12_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).2 3).1 1).1
      183217879999924166044574149886131629253068131484000493076493401868340120215595687347199109783742445334121854313768).isSome = true := by
  decide +kernel

theorem k12_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).2 3).1 1).2 2).1
      221590717259597000370433172588715193783917429196497721906720461300706178708120953683665922143975186107262763052200).isSome = true := by
  decide +kernel

theorem k12_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).2 3).1 1).2 2).2
      595208762937122392643589369961240037352703757257541531300751789331219043697374215321379401460235097865398238312).isSome = true := by
  decide +kernel

theorem k12_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).2 3).2 1).1
      173464382652464729626422449004049582153068287400234609920835364372489932142515895522561512720580664937528708605224).isSome = true := by
  decide +kernel

theorem k12_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).1 3).2 1).2 2).2 3).2 1).2
      183196743115081893351792518536260765015830362149047197338882491217105216798125708873962442738265436709984866262856).isSome = true := by
  decide +kernel

theorem k12_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).1 2).1 3).1 3).1
      20175792556138947509740053317657524631037321353666730413359074116104590280616522824886942690220635194051874646136806248).isSome = true := by
  decide +kernel

theorem k12_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).1 2).1 3).1 3).2
      173511353508623277073403284213366059326925906620752244922878368109966892958012302071106156232027861066765963102184).isSome = true := by
  decide +kernel

theorem k12_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).1 2).1 3).2 3).1
      171162810924718293462692860728823788261300705225270867785785834339721877208412687210623206850039058365901125540072).isSome = true := by
  decide +kernel

theorem k12_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).1 2).1 3).2 3).2
      168682749956387951260829157439477915395075601444023385573614016448109888507938328623601170761507239720247067990248).isSome = true := by
  decide +kernel

theorem k12_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).1 2).2 3).1 3).1
      190178960218895071850295309163516864985555007838927981985804816717704816716907281748837649568309162078430061838504).isSome = true := by
  decide +kernel

theorem k12_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).1 2).2 3).1 3).2
      173567718529718202642928156986647405692468263736639853294345004165435451369722497523582286832127569837093203591336).isSome = true := by
  decide +kernel

theorem k12_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).1 2).2 3).2 3).1
      341566165919458276530141057380360435233169824400420662726674800839865026681890418470910525106814142232424628392).isSome = true := by
  decide +kernel

theorem k12_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).1 2).2 3).2 3).2
      567026253057967232945070756957448329984478354814216322866000065477631772621507604390690858700234582747577630888).isSome = true := by
  decide +kernel

theorem k12_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).2 2).1 3).1 1).1 3).1
      520055404783023266684771321566647318991802275624007841731892421510062781657500564136356576234262956195314394056).isSome = true := by
  decide +kernel

theorem k12_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chBCellBox 12) 1).1 2).2 3).1 1).2 2).1 3).1 1).1 3).2
      332171996786429527717802488559581807628989756319291105156002513008024425532248619402834093734838922421505969032).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChB004
