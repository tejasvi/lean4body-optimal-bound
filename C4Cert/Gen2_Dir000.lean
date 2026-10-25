module

public import C4Check

public section

/-! Pieces of cell `1` of the direct root grid: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_Dir000

theorem k1_0 : (checkBoxH2 dirModeTFM depth (splitBox (dir2CellBox 1) 1).1
      3169).isSome = true := by
  decide +kernel

theorem k1_1 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).1
      3245153).isSome = true := by
  decide +kernel

theorem k1_2 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).1 2).1 3).1
      3).isSome = true := by
  decide +kernel

theorem k1_3 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).1 2).1 3).2 1).1
      462794529921708179219747597045162040206576870237574603822180279451250886392474659609593158778059885026939866914915).isSome = true := by
  decide +kernel

theorem k1_4 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).1 2).1 3).2 1).2 2).1
      238214562227079972880772246653592802193547806497690297520399092023010403120625872707348016699203927836679970364734722210966492208335076864368823941304082328168107295454109806290916974582085792479708743109905336577294714149048847362211).isSome = true := by
  decide +kernel

theorem k1_5 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).1 2).1 3).2 1).2 2).2
      238214573433445123458012375180609663190419308614695940900458074283118947770602326647160777283143907549761153552018533001204208989938611984121735721651187759765628773544025077137005342925138907298326891743479675948271940665769913542819).isSome = true := by
  decide +kernel

theorem k1_6 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).1 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k1_7 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).1 2).2 3).2 1).1
      501273102676933311313145607118487697778371889879116431762974482479735305939584246261182260091562224801899445952611).isSome = true := by
  decide +kernel

theorem k1_8 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 3).1
      360863560771339554248362180966936996889016707222650762941913407816161181797066812738647034220481411751086249607121370816955108494230203271858107221192266574370388801892162635332199754171588687957626612755351643082389797189777908313763).isSome = true := by
  decide +kernel

theorem k1_9 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).1 2).2 3).2 1).2 3).2
      82005089001150525601585143271096153354237495236312262364014778180845140749780634242347861886464149510720175627560).isSome = true := by
  decide +kernel

theorem k1_10 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).1 3).1 1).1
      7026701352323373126076260016361267801144582439117400715324578101467999556294851106778866296864814293668915762306613632539281000607631577527846136683323583236075057571215652131659799875701268267822759736546367007508599781804126525981763).isSome = true := by
  decide +kernel

theorem k1_11 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).1
      81203585618025246357085730434935818182513063565240411612464009418650584297468185900456624958336134252161380435154057746908008264139842730773452438847119473839313951006028250849405719327451891611024101037770961459095657311488408253497379).isSome = true := by
  decide +kernel

theorem k1_12 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).1 3).1 1).2 2).2
      84383142686463879176543545094386345868483702378358347557820554168721661796077859984600009313123425215341211462162118767165929326389031868455188470824611797124587514463154259475414991930449409458524909509068395223802840784063010051719203).isSome = true := by
  decide +kernel

theorem k1_13 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).1 3).2 1).1 2).1
      86021937018356024674715074659343664763732532048130730677754245860314173002688824461209717197544625661276356907484557059450529859915279255430187112762541109670107769779254526366013597861611591704639500787017353299467300783787179847336739).isSome = true := by
  decide +kernel

theorem k1_14 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).1 3).2 1).1 2).2
      86021939131236819101014769050734252131469071062374944611471400179600099033158808867748355277331309219816344146236647591906918173965578079964105874702943999763445579169212602250025464151728692124124739330483448089278706394155417954304803).isSome = true := by
  decide +kernel

theorem k1_15 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).1 3).2 1).2 3).1 3).1
      130091498345892195010432931099702441330418377769803557623296680485258556678654041661495589593016192510258941329416).isSome = true := by
  decide +kernel

theorem k1_16 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).1 3).2 1).2 3).1 3).2
      2284061390959707072061271504081225879267230012191475278238848092048065441413836565249752459713301599108891094467928).isSome = true := by
  decide +kernel

theorem k1_17 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).1 3).2 1).2 3).2
      145490747590429194687353626652592095941478409722210293429771167156186675412814944920443961367907863280694909483364472).isSome = true := by
  decide +kernel

theorem k1_18 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).1 1).1
      9411371431766209998502792354750321104580033933572316553104666610712184112393980665469989666402141490159592193022284968172965216010296820341765881585490123250028314664893174962778314391566709536669385094322686528687285686109186476213315).isSome = true := by
  decide +kernel

theorem k1_19 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).1 1).2 2).1 3).1
      101206773320400652498822006702799498804117701342023156897708234803761291137890993319801827564788871677976644976648).isSome = true := by
  decide +kernel

theorem k1_20 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).1 1).2 2).1 3).2
      134863736950678215717446469597639100529199474606756627667511807438334146671468136598501204410105802932558247231496).isSome = true := by
  decide +kernel

theorem k1_21 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).1 1).2 2).2 3).1
      354653573060427161748391282757305456636471093624298355068115467277145092980132456255570967546751536810755584943882450160900322967575094098769226098396809797577274051999820619058311710563463195564767680935842814093928498598297559367715).isSome = true := by
  decide +kernel

theorem k1_22 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).1 1).2 2).2 3).2
      146907063349559027716397047455838421254531142865234441991219990106338272563180059099122527609482093863348195753992).isSome = true := by
  decide +kernel

theorem k1_23 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).2 1).1 2).1
      344087766250153705345634858629674504045838054539585510134250741480652570844445747995318933167786337728519261263605430577714814035144027762238745551427840335840101433497511438664833049330446761617512125937967693391036147856424998481445667).isSome = true := by
  decide +kernel

theorem k1_24 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).2 1).1 2).2
      5607150266320422672114873943962478839102839386578990312467103517574139915901520419214639032113620411224407932779844615656819370820378807333848161986268155581952827732526216309969068643372030540220143637676898567101904307926360237908968227).isSome = true := by
  decide +kernel

theorem k1_25 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).2 1).2 3).1 3).1
      134891919421650965103411883744036288845553458867415843286500675755047266669140738981742222632592088312136199962632).isSome = true := by
  decide +kernel

theorem k1_26 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).2 1).2 3).1 3).2
      275475016736203506371749668316382241274862218315271585603366903918320645586807770252099711096581187562450586045312345509818675813351999647243945135006414388974632920422087133199523534436246337251076998217091095790615583798448866284962).isSome = true := by
  decide +kernel

theorem k1_27 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).1 3).2 1).2 2).2 3).2 1).2 3).2
      2445711673671282608859520629521424765857142165920167571635661938854819756690670998593691855069054358697678274505675896).isSome = true := by
  decide +kernel

theorem k1_28 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).1
      3245153).isSome = true := by
  decide +kernel

theorem k1_29 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).1 2).1 3).1
      3).isSome = true := by
  decide +kernel

theorem k1_30 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).1 2).1 3).2 1).1
      578230229754564316766064524711287448613851806217454167553205780955500189414246739687114701362797275322272148037731).isSome = true := by
  decide +kernel

theorem k1_31 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).1 2).1 3).2 1).2 3).1
      230452111680692822623916133274995360955266448295676603605766360083218953396359116142205850483244185295838743307107399751076094685228574906306071723382410582201274293906273584223812271805078019351219640949007753862797369826491626434211).isSome = true := by
  decide +kernel

theorem k1_32 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).1 2).1 3).2 1).2 3).2
      98877018977812043086033426633153994895922238760190461118666831700705116421235407008923698110380136546812565216552).isSome = true := by
  decide +kernel

theorem k1_33 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).1 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k1_34 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).1 2).2 3).2 1).1
      414696668877829685375612436459560938176453965998860525011540555925838607940890391642900819415240204695682619482211).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_Dir000
