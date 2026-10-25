module

public import C4Check

public section

/-! Pieces of cell `15` of the chart root grid A: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChA041

theorem k15_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).1
      3).isSome = true := by
  decide +kernel

theorem k15_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).1
      99).isSome = true := by
  decide +kernel

theorem k15_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).1
      12674).isSome = true := by
  decide +kernel

theorem k15_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 1).1 2).1
      7133336735646922887677764978448029170494478656402528956368743407541035816543154444197161793946934743181209227487030225066988218184943433925000587309916565681617199513656872193867073947598075579979186017454437383664758448953669254838178179).isSome = true := by
  decide +kernel

theorem k15_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 1).1 2).2 3).1
      30491460844980668862432376494721645248965280894717018198087174226971826903555068483574352105331632640756438959208252824534348462299197020147748266749046754039122315205536912932075146504832716657652240388083693041486237183396730550702091).isSome = true := by
  decide +kernel

theorem k15_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 1).1 2).2 3).2 3).1
      166362389928365336989861489433740758053368785544863799059160756661007883906829337254841881352940465435158263088840).isSome = true := by
  decide +kernel

theorem k15_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 1).1 2).2 3).2 3).2
      178180256193283933438029745468920524992956926889338128800471055207798638859596984461503112570233953824099532179880).isSome = true := by
  decide +kernel

theorem k15_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 1).2 2).1
      7540320041360658870194259403455450937274791590245268986252613737456158834272064104927154265737268514817745678724472834869562905728512297486400161578405334385602791303047273881186095739248577381077494316059192223961247353910395996871152003).isSome = true := by
  decide +kernel

theorem k15_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).1
      33671017973216419141585382584019365932841800005700786411679376253636387580797587014394026883539971942638636509619331705493421132331992511668167957561994625540036350601749971158782679997144079713780680271615306632059710231322774932393995).isSome = true := by
  decide +kernel

theorem k15_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).2 3).1
      173323470144046412649055521739742106705680752425374989969029962492006401959486700226949648246889110085717130368648).isSome = true := by
  decide +kernel

theorem k15_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).2 3).2
      122914352135534504126801709846675573286258511847054836509454773037036140786474681013966237388239243093323082267464).isSome = true := by
  decide +kernel

theorem k15_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).1
      99).isSome = true := by
  decide +kernel

theorem k15_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).2 3).1
      12674).isSome = true := by
  decide +kernel

theorem k15_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 1).1 2).1
      975726703180592773267892976607926563600861265144412970929332963246778716731786050379497290830638901518063731698553204840257137091254643870352317167718514603545945999523788750164012494523441270543629242742256883384273320610692396488459651).isSome = true := by
  decide +kernel

theorem k15_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 1).1 2).2 3).1
      36850575100873811360028917334961569039549625594165314858167872209043839890466548848933636155689026730116810884270592143060518883005103228922039778570479128846286357047267581138341544558805104037657549895409574479990219302089360712273931).isSome = true := by
  decide +kernel

theorem k15_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 1).1 2).2 3).2
      87611707110259965343375372285714220735464005189873425800654587250512475091171597080136371951675421266984260807844509598403740053538291833752570168921244241568067227971579000107119080016653826448854160135537970520720217785526065265291427).isSome = true := by
  decide +kernel

theorem k15_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 1).2 2).1
      1905710444288962722701746822590799779745530916067839840423869892464606507103152132895492995454444424448499460814061507151062335133108862013054996146497458801943146148901971351712920157081694947928072157820262217178982276793260785920656278915).isSome = true := by
  decide +kernel

theorem k15_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 1).2 2).2 3).1
      9985485871795985087906516017786836736329212417203791665154409819827453291455728960153378589771161599721439767355551290033535742911282648782109757471087258155905785407429478497391741533687252519820715079546259905857202662781250430222127115).isSome = true := by
  decide +kernel

theorem k15_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 1).2 2).2 3).2 3).1
      122895563807407789125506491550030163137624544368580913093230753707576303232621108973978915275555515612715447224744).isSome = true := by
  decide +kernel

theorem k15_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).1 3).2 1).2 2).2 3).2 1).2 2).2 3).2 3).2
      140348914039553928882765488868537764806605357116372317559880983559631637825092587366049964888610648659617072655448).isSome = true := by
  decide +kernel

theorem k15_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).1 3).1
      0).isSome = true := by
  decide +kernel

theorem k15_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).1 3).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k15_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).1 3).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k15_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).1 3).2 3).2 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k15_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).1 3).2 3).2 2).2 3).2 1).1
      59932147980979605037285386906221493436816663589189198667611832911617069578903133177936124064257354402876897912062258163609271049400684651839108559807421062995302942162918736525794240524996567794894133892705372723278784439158780107443456373211193).isSome = true := by
  decide +kernel

theorem k15_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).1 3).2 3).2 2).2 3).2 1).2
      65053184718813421596803231014915367934999922125459166865950518473146134836086074190228742120763150806652940740671085485083795521941735855358739820881513494869796436416179272285129066810358854262897819434470737780547135041470195078367055834038329).isSome = true := by
  decide +kernel

theorem k15_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k15_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).1 3).1
      24).isSome = true := by
  decide +kernel

theorem k15_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).1 3).2 2).1 1).1
      210546349024948283773481740270050030201790256124642683372432716007241884040498399662012138704688612010100804522469395103062724822112035627500385736591191795487891360428781571490539750257721680546962993240554606284794402093066941664863246).isSome = true := by
  decide +kernel

theorem k15_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).1 3).2 2).1 1).2
      216905463554555161448372136044217194032591770847354327788401393650595325645969656029089428943738551772719769977236368787290454919256977072226486760311932092265723575311091302804632445443071577831171340582091478753836224282727180410954766).isSome = true := by
  decide +kernel

theorem k15_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).1 3).2 2).2
      15388563159617870486591051782977496576449239986826246994211388400587614638017673187258237721566456875539977266462167222941330031986830519786147311614043614346221337409799335934347871815114539764829520485818300276466957459134107512115211).isSome = true := by
  decide +kernel

theorem k15_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 3).1
      24).isSome = true := by
  decide +kernel

theorem k15_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 3).2 2).1 1).1
      223264578075787414427454235726386115246781195871643252563806295644779925281984325794588024312647451987251501669185696270029545088552375314486671991642476724631880862648622160864076785217660644065325896013292507823790697610739648100631566).isSome = true := by
  decide +kernel

theorem k15_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 3).2 2).1 1).2
      223264578482349995688644986987919333405033856057932620419901895160095042776547653900140101764606932364072986987463581264242905530129606138519040490673703806868665516439642751122675598800710184437187615132236337293920815532487787440661518).isSome = true := by
  decide +kernel

theorem k15_34 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 3).2 2).2
      12429770354400856621629220109003797391024659477374010679955606526604545347595715879522566449291052413338240472351520673575185777638239449202975198053052794173815065138176427546037264467752295545371961049485590957820556180255659027370676235).isSome = true := by
  decide +kernel

theorem k15_35 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).2 2).1 3).1
      0).isSome = true := by
  decide +kernel

theorem k15_36 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).2 2).1 3).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k15_37 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).2 2).1 3).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k15_38 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 15) 1).1 2).2 3).1 1).2 2).1 3).2 3).2 2).2 3).1
      0).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChA041
