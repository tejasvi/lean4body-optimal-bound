module

public import C4Check

public section

/-! Pieces of cell `17` of the chart root grid A: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChA076

theorem k17_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).1 1).1 2).1
      0).isSome = true := by
  decide +kernel

theorem k17_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).1 1).1 2).2 3).1 3).1 1).1 2).1
      1845367334867983872254572721640875232014454899196770056591489005066143762293694227667198881935601893173098941987).isSome = true := by
  decide +kernel

theorem k17_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).1 1).1 2).2 3).1 3).1 1).1 2).2
      304972771200017714441762041349180276286251864331569854529253918688752706518975780215862598646600825795140863850797077814134193556000733558044728791157341348869842867151072959420863728807528582190391800113298142838789718930806381754659).isSome = true := by
  decide +kernel

theorem k17_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).1 1).1 2).2 3).1 3).1 1).2
      61456662166282219028446723097830275564468930949150818223824331002304058712424821712024695119230508236631297217634).isSome = true := by
  decide +kernel

theorem k17_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).1 1).1 2).2 3).1 3).2
      0).isSome = true := by
  decide +kernel

theorem k17_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).1 1).1 2).2 3).2
      0).isSome = true := by
  decide +kernel

theorem k17_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).1 1).2
      0).isSome = true := by
  decide +kernel

theorem k17_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).1 1).1 2).1 3).1
      27271276324573646148085684436880248313543450336562791673086827408141899564813342569581461544364458885555279045400).isSome = true := by
  decide +kernel

theorem k17_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).1 1).1 2).1 3).2
      185385584797578104503894458827319842238731701087064681677156974297809200998063903098773631187000780757856508022344).isSome = true := by
  decide +kernel

theorem k17_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).1 1).1 2).2
      893058073948930833704506821651698371805232676002968159887043261133622847782447519100240536279719726455627333912923412345236782605723213989857789758437770595090447360778037106822096742810229053395414958624116072013219441153740837793516643).isSome = true := by
  decide +kernel

theorem k17_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).1 1).2 2).1
      317392914940349076598082271939563491024063891044059496062961063142363734206029277241671864901866151201061605904039009796214727233037014053688790996450387124146694616823248510263000972239191112475798499814334905812700224775447084012963).isSome = true := by
  decide +kernel

theorem k17_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).1 1).2 2).2 3).1
      27872503129730317144570148616581148984938177291998321088209668285427708279705311726349758703531517561121896672024).isSome = true := by
  decide +kernel

theorem k17_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).1 1).2 2).2 3).2
      79372372609458277913586204833379087168789060467764663181986027217843279376009979803245775374250144626808357225832).isSome = true := by
  decide +kernel

theorem k17_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).2 1).1 2).1
      10253736707450149483398158770876817397639999548812074811326421451208884282612331276449838178440809821035792462082).isSome = true := by
  decide +kernel

theorem k17_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).2 1).1 2).2
      323602983967907490925090780376268893108271967419008067168647069155407799703509503630261658449488896600746798779685109372992308015193093577385400849911573711837865322844572575287857075898549809961078861862275673100297112508018449463587).isSome = true := by
  decide +kernel

theorem k17_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).1 3).2 1).2
      63861568976983121113040354780888238077125723595394312818530610295754284883162273144748339112042368335253722354786).isSome = true := by
  decide +kernel

theorem k17_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).1 1).1 2).1
      5607589777897493295618981105360669890094545389622274241648352454924326629119544265091987508836638807048902815165260003891195721549642623822647195638629701221726217304320906819025140319511638928195181094780682997222132332612338605155085411).isSome = true := by
  decide +kernel

theorem k17_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).1 1).1 2).2 3).1
      122895563752885028320388603917654966075766355073835461054448330449850455376942575681390520364488140758168790846408).isSome = true := by
  decide +kernel

theorem k17_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).1 1).1 2).2 3).2
      153682747782291716533610643056814267884670274156660069210647157710137743237178082295825703010888439370947611592).isSome = true := by
  decide +kernel

theorem k17_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).1 1).2 2).1
      816748699510364745375030841369114756506040088505128959751736479993028419482397890481793735654102896310879467307535197392622688849613350567660585341975716418319141133566208442999395185289861533122624869783531762037316848421664081775971427).isSome = true := by
  decide +kernel

theorem k17_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).1 1).2 2).2
      135826697239299167672216124069796740996835231593893185477636811743450914198620497014809218901286593832363406993638494654540013779414088708074214431086785100545621522741975565769347877462841097045448377478981272439520928286792590016824675).isSome = true := by
  decide +kernel

theorem k17_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).2 1).1 2).1
      242872042021675775315225889397045442119354189427687499389029670433000246149696008535363026603088844267779410226701752193500099641544326328401570801566892452448686068348656372929316440024883929873611821943297621850892800331626673977123).isSome = true := by
  decide +kernel

theorem k17_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).2 1).1 2).2
      91631764886035316408189803015596013631962206116385507153041772677536822665551124160571865077688318950622294395848).isSome = true := by
  decide +kernel

theorem k17_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 2).1
      354653343726274998658235255510828571671757848165400119522050013728864417966814201497963069289569623466764326572294281108007919591004558452438699095128869981467056842910989521315735500336047613869000071330363517017474131991492388086307).isSome = true := by
  decide +kernel

theorem k17_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 2).2
      199401533055414776128673277755506022013310676038006069107516258937932596760517688226460642926124339348325117352874584669087540374221870759897458949598558855892249174459095126975101573189375275035257584060952217349679835364299677848995).isSome = true := by
  decide +kernel

theorem k17_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).2 2).1 3).1 1).1 2).1
      2371440862895208281835219196264308640138076951701709217122370291830000965900889047813679331511202373687663120291).isSome = true := by
  decide +kernel

theorem k17_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).2 2).1 3).1 1).1 2).2
      12761698476803448089454627533487545467136697932726990347148213613221740176711168032155694246348741431595830749378337081183873324658848484114349495967663632464016709126192790373050418578588279838907153816478403392757266642583362493852771).isSome = true := by
  decide +kernel

theorem k17_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).2 2).1 3).1 1).2
      54542552402722876534864834443833975733575872123492758598255833392689304860778261601964639442679562527822663939170).isSome = true := by
  decide +kernel

theorem k17_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).2 2).1 3).2
      0).isSome = true := by
  decide +kernel

theorem k17_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).2 2).2 3).1 1).1 2).1
      3775723919854246564682408276733347459793842002737190776665327959037703988281597418193131766907708125507802222172258684343025801074674298310225859710052434992280657800624982272445452721069021699978823724103629721958900829107029553585163363).isSome = true := by
  decide +kernel

theorem k17_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).2 2).2 3).1 1).1 2).2
      22835752635350028459711546333807930992132613591388914598000956845615512210541790537191275847519333257101041652346957737543104856143544510611638623542658822738546596507286407290244167331699302811505301456823707213785255563831723851223445859).isSome = true := by
  decide +kernel

theorem k17_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).2 2).2 3).1 1).2 2).1 3).1
      26670049189750171423547849660365452795425620619178234008379124477489225393917682437638741790350126811517235180312).isSome = true := by
  decide +kernel

theorem k17_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 17) 1).1 2).2 3).1 1).2 2).2 3).1 1).2 2).1 3).2
      153682747229122335402437799850129740548309302432835594956358938941192129047734379605454387534643206052356049128).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChA076
