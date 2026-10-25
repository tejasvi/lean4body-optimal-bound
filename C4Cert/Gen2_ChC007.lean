module

public import C4Check
public import C4Cert.Gen2_ChC002
public import C4Cert.Gen2_ChC003
public import C4Cert.Gen2_ChC004
public import C4Cert.Gen2_ChC005
public import C4Cert.Gen2_ChC006

public section

/-! Cells `13 ≤ n < 15` of the chart root grid C: `decide +kernel` checks that `checkBoxH2` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChC007

theorem k13_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).1
      3).isSome = true := by
  decide +kernel

theorem k13_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k13_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k13_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k13_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).1
      161392465177186753303056863755518884609143314370155546206463094507652112566887640338001851352510227147437830356272544232).isSome = true := by
  decide +kernel

theorem k13_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k13_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).1
      80697156618489240602275136782105508334002154126914658686448585259902971881836703711751554832941526455205841597626460552).isSome = true := by
  decide +kernel

theorem k13_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).1
      322783082670348579478028678604655703174576461161649437457265846171196202821643220641313405369656539768155754770298171816).isSome = true := by
  decide +kernel

theorem k13_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).1
      20175675204163193697784293360286930499207717435675235265225792464754949989090004825865132524447350367989690429990576648).isSome = true := by
  decide +kernel

theorem k13_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).1 2).1
      40349502677330616109287194844243441873096218088704656344154334340244781383945340654644476791300470670273993679884664520).isSome = true := by
  decide +kernel

theorem k13_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).1 2).2 3).1
      1908218982392133559795042729126650264352580199663097945152821421783402841685711218101134202960637230085311208).isSome = true := by
  decide +kernel

theorem k13_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).1 2).2 3).2 3).1
      5045305444762953594520268283942493507362498524504017875284464026113161771474108795951763808074000568790899637264097608).isSome = true := by
  decide +kernel

theorem k13_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).1 2).2 3).2 3).2 1).1 2).1
      1321082469043653105087054763266834152351020593158433660630616454400445814471192952574293850767270447736039400).isSome = true := by
  decide +kernel

theorem k13_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).1 2).2 3).2 3).2 1).1 2).2
      1526882931922837107452244940698555481772700299371438000710983754529371655664939874373232112189439472078454137270927228498934123144667508605996983122970527665505343559482880907080492879731844979352110750884752818028728687674835277316456483).isSome = true := by
  decide +kernel

theorem k13_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).1 2).2 3).2 3).2 1).2 1).1
      1491096613275117842900274087717011157875109552297084360267919751588713413479673866381436085583336096002790772205208809645532679999676412275113680359394554163256865251724580432185227031881560123657261300080325061453190645922839394201123).isSome = true := by
  decide +kernel

theorem k13_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).1 2).2 3).2 3).2 1).2 1).2
      2377752608528420219958676518506742933995573813543114777596876276866366281327684897277506023723783267776340069896).isSome = true := by
  decide +kernel

theorem k13_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).2 3).1
      1532277279946635177030455618256965130283319999383704326445389246322931087125196298445853244819621150615825108872).isSome = true := by
  decide +kernel

theorem k13_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).2 3).2 1).1
      1360685093763864992564402266228094420980469164418347422482740837258768739809050992304659931621957569721464222220955446485742305925279864030892760416202718336436364937222527218826376121251888297152252573480573274824767403606021837253667).isSome = true := by
  decide +kernel

theorem k13_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).1 2).2 3).2 3).2 2).2 3).2 2).2 2).2 2).2 3).2 1).2 3).2 1).2
      1908044092503173304577179764484166735273862569990604302641726035686759342616265840680267368884877613809146511144).isSome = true := by
  decide +kernel

theorem k13_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).1
      3).isSome = true := by
  decide +kernel

theorem k13_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k13_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k13_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k13_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).2 3).2 2).2 2).1
      645564317177569559868729497426624241899097532154075957144225891839606260951308486654872133721900537456704265601148329000).isSome = true := by
  decide +kernel

theorem k13_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).2 3).2 2).2 2).2 3).1
      80697156411817497659733799488100812954550631493850924587907010932028466892231271170782315047722562938273935768552808488).isSome = true := by
  decide +kernel

theorem k13_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).2 3).2 2).2 2).2 3).2 2).1
      161392465318099305318338816078372332324221849821080169535604486064088534368203979559423654771385938968523970967226588968).isSome = true := by
  decide +kernel

theorem k13_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).2 3).2 2).2 2).2 3).2 2).2 3).1
      1100145446826741758185326380885385643953629328339917491575817368747576738369750208264510525817297616972661183432).isSome = true := by
  decide +kernel

theorem k13_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).2 3).2 2).2 2).2 3).2 2).2 3).2 1).1
      1068811692920286804476324936575291925143936423867096200712206424897631485943551956783517688259739777608702397034529735152311841484224228572951191801395727669979173663921938958834764048264146149539033203813053173357866045957186510508579).isSome = true := by
  decide +kernel

theorem k13_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).1 1).2 2).2 3).2 3).2 2).2 2).2 3).2 2).2 3).2 1).2
      1485306428743919412369084903045137381716902636032270160970915439942592724215289386054516087140600337063336030120).isSome = true := by
  decide +kernel

theorem k13_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).1 2).1
      3).isSome = true := by
  decide +kernel

theorem k13_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).1 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k13_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).1 2).2 3).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k13_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).1 2).2 3).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k13_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).1 2).2 3).2 3).2 2).2 2).1
      1291126786736873390131399322636310643099049141852205967446494895806516157767718464445673378982525184504738732219996050344).isSome = true := by
  decide +kernel

theorem k13_34 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).1 2).2 3).2 3).2 2).2 2).2 3).1
      10088761326666932991269004843766478054473472339038403739370267431974921495676972778592191896781863760391008025021579752).isSome = true := by
  decide +kernel

theorem k13_35 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).1 2).2 3).2 3).2 2).2 2).2 3).2 3).1
      1194087151626529315095837599831604260175809536842167743577825689371935401186270407282968433622884858770073400392).isSome = true := by
  decide +kernel

theorem k13_36 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).1 2).2 3).2 3).2 2).2 2).2 3).2 3).2
      857669233572724731151207029823457902530638402442994613929254606009687194318592583214408050679271287741398027252409752686984119288638909332152084992819786206064902047534202457156298010329353112685219735446081056879849643731399988139425).isSome = true := by
  decide +kernel

theorem k13_37 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).2 2).1
      3).isSome = true := by
  decide +kernel

theorem k13_38 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).2 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k13_39 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).2 2).2 3).2 3).1
      165264051317739292251853942125149086480698833880076233630415905600298992357892188943820279336191888153485291145753534696707).isSome = true := by
  decide +kernel

theorem k13_40 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).2 2).2 3).2 3).2 2).1
      0).isSome = true := by
  decide +kernel

theorem k13_41 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).2 2).2 3).2 3).2 2).2 2).1
      10329001359778016686023205399874455582163616777977412200865398900610623647912027120859280974113337746199088913481571676648).isSome = true := by
  decide +kernel

theorem k13_42 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).2 2).2 3).2 3).2 2).2 2).2 3).1
      790137832270074938757949109612070836963705827988297374111880707038235418317319347122279394680480045132312642920).isSome = true := by
  decide +kernel

theorem k13_43 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 13) 1).2 1).2 2).2 3).2 3).2 2).2 2).2 3).2
      615476411389162145670281092044375491842468388474622725014031137088484469082548322475853466927049045416639837460508994913700805144053023295530385879529261044767300639431072459621056209837788976800805603452896580915413324767710810791843).isSome = true := by
  decide +kernel

theorem cover : Cover2 (chModeTFM 7) chCCellBox 13 15 :=
  (Cover2.one (box := chCCellBox) (n := 13)
      (.split 1 (.split 1 (.split 2 (.leaf _ k13_0) (.split 3 (.leaf _ k13_1) (.split 3 (.leaf _ k13_2) (.split 2 (.leaf _ k13_3) (.split 3 (.leaf _ k13_4) (.split 2 (.leaf _ k13_5) (.split 2 (.leaf _ k13_6) (.split 2 (.leaf _ k13_7) (.split 3 (.leaf _ k13_8) (.split 1 (.split 2 (.leaf _ k13_9) (.split 3 (.leaf _ k13_10) (.split 3 (.leaf _ k13_11) (.split 1 (.split 2 (.leaf _ k13_12) (.leaf _ k13_13)) (.split 1 (.leaf _ k13_14) (.leaf _ k13_15)))))) (.split 3 (.leaf _ k13_16) (.split 1 (.leaf _ k13_17) (.leaf _ k13_18))))))))))))) (.split 2 (.leaf _ k13_19) (.split 3 (.leaf _ k13_20) (.split 3 (.leaf _ k13_21) (.split 2 (.leaf _ k13_22) (.split 2 (.leaf _ k13_23) (.split 3 (.leaf _ k13_24) (.split 2 (.leaf _ k13_25) (.split 3 (.leaf _ k13_26) (.split 1 (.leaf _ k13_27) (.leaf _ k13_28))))))))))) (.split 1 (.split 2 (.leaf _ k13_29) (.split 3 (.leaf _ k13_30) (.split 3 (.leaf _ k13_31) (.split 2 (.leaf _ k13_32) (.split 2 (.leaf _ k13_33) (.split 3 (.leaf _ k13_34) (.split 3 (.leaf _ k13_35) (.leaf _ k13_36)))))))) (.split 2 (.leaf _ k13_37) (.split 3 (.leaf _ k13_38) (.split 3 (.leaf _ k13_39) (.split 2 (.leaf _ k13_40) (.split 2 (.leaf _ k13_41) (.split 3 (.leaf _ k13_42) (.leaf _ k13_43)))))))))).trans <|
  (Cover2.one (box := chCCellBox) (n := 14)
      (.split 1 (.split 1 (.split 2 (.leaf _ C4.Cert.Gen2_ChC002.k14_0) (.split 3 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC002.k14_1) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC002.k14_2) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC002.k14_3) (.split 1 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC002.k14_4) (.split 1 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC002.k14_5) (.split 1 (.leaf _ C4.Cert.Gen2_ChC002.k14_6) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChC002.k14_7) (.split 3 (.leaf _ C4.Cert.Gen2_ChC002.k14_8) (.leaf _ C4.Cert.Gen2_ChC002.k14_9))) (.split 3 (.leaf _ C4.Cert.Gen2_ChC002.k14_10) (.leaf _ C4.Cert.Gen2_ChC002.k14_11))))) (.split 3 (.leaf _ C4.Cert.Gen2_ChC002.k14_12) (.leaf _ C4.Cert.Gen2_ChC002.k14_13))) (.split 3 (.split 1 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC002.k14_14) (.split 1 (.leaf _ C4.Cert.Gen2_ChC002.k14_15) (.leaf _ C4.Cert.Gen2_ChC002.k14_16))) (.leaf _ C4.Cert.Gen2_ChC002.k14_17)) (.split 3 (.leaf _ C4.Cert.Gen2_ChC002.k14_18) (.leaf _ C4.Cert.Gen2_ChC002.k14_19))) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChC002.k14_20) (.leaf _ C4.Cert.Gen2_ChC002.k14_21)) (.leaf _ C4.Cert.Gen2_ChC002.k14_22))))) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChC002.k14_23) (.leaf _ C4.Cert.Gen2_ChC002.k14_24)) (.leaf _ C4.Cert.Gen2_ChC002.k14_25))) (.split 3 (.split 1 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC002.k14_26) (.split 1 (.leaf _ C4.Cert.Gen2_ChC002.k14_27) (.leaf _ C4.Cert.Gen2_ChC002.k14_28))) (.split 1 (.leaf _ C4.Cert.Gen2_ChC002.k14_29) (.leaf _ C4.Cert.Gen2_ChC002.k14_30))) (.split 3 (.leaf _ C4.Cert.Gen2_ChC002.k14_31) (.leaf _ C4.Cert.Gen2_ChC002.k14_32))) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChC002.k14_33) (.leaf _ C4.Cert.Gen2_ChC002.k14_34)) (.leaf _ C4.Cert.Gen2_ChC002.k14_35))))) (.split 1 (.leaf _ C4.Cert.Gen2_ChC003.k14_36) (.split 3 (.leaf _ C4.Cert.Gen2_ChC003.k14_37) (.leaf _ C4.Cert.Gen2_ChC003.k14_38))))) (.split 3 (.leaf _ C4.Cert.Gen2_ChC003.k14_39) (.leaf _ C4.Cert.Gen2_ChC003.k14_40)))) (.split 3 (.leaf _ C4.Cert.Gen2_ChC003.k14_41) (.leaf _ C4.Cert.Gen2_ChC003.k14_42))) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChC003.k14_43) (.leaf _ C4.Cert.Gen2_ChC003.k14_44)) (.leaf _ C4.Cert.Gen2_ChC003.k14_45)))) (.split 2 (.leaf _ C4.Cert.Gen2_ChC003.k14_46) (.split 3 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC003.k14_47) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC003.k14_48) (.split 3 (.split 1 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC003.k14_49) (.split 1 (.leaf _ C4.Cert.Gen2_ChC003.k14_50) (.leaf _ C4.Cert.Gen2_ChC003.k14_51))) (.split 1 (.leaf _ C4.Cert.Gen2_ChC003.k14_52) (.leaf _ C4.Cert.Gen2_ChC003.k14_53))) (.split 3 (.leaf _ C4.Cert.Gen2_ChC003.k14_54) (.split 1 (.leaf _ C4.Cert.Gen2_ChC003.k14_55) (.leaf _ C4.Cert.Gen2_ChC003.k14_56)))) (.split 1 (.split 3 (.split 3 (.leaf _ C4.Cert.Gen2_ChC003.k14_57) (.leaf _ C4.Cert.Gen2_ChC003.k14_58)) (.leaf _ C4.Cert.Gen2_ChC003.k14_59)) (.split 3 (.leaf _ C4.Cert.Gen2_ChC003.k14_60) (.leaf _ C4.Cert.Gen2_ChC003.k14_61))))) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChC003.k14_62) (.split 1 (.leaf _ C4.Cert.Gen2_ChC003.k14_63) (.leaf _ C4.Cert.Gen2_ChC003.k14_64))) (.leaf _ C4.Cert.Gen2_ChC004.k14_65)))) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC004.k14_66) (.leaf _ C4.Cert.Gen2_ChC004.k14_67)) (.leaf _ C4.Cert.Gen2_ChC004.k14_68))) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChC004.k14_69) (.leaf _ C4.Cert.Gen2_ChC004.k14_70)) (.split 3 (.leaf _ C4.Cert.Gen2_ChC004.k14_71) (.leaf _ C4.Cert.Gen2_ChC004.k14_72)))))) (.split 1 (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChC004.k14_73) (.split 1 (.leaf _ C4.Cert.Gen2_ChC004.k14_74) (.leaf _ C4.Cert.Gen2_ChC004.k14_75))) (.split 3 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC004.k14_76) (.split 3 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC004.k14_77) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChC004.k14_78) (.leaf _ C4.Cert.Gen2_ChC004.k14_79)) (.leaf _ C4.Cert.Gen2_ChC004.k14_80))) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChC004.k14_81) (.leaf _ C4.Cert.Gen2_ChC004.k14_82)) (.split 3 (.leaf _ C4.Cert.Gen2_ChC004.k14_83) (.leaf _ C4.Cert.Gen2_ChC004.k14_84)))) (.split 3 (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChC004.k14_85) (.leaf _ C4.Cert.Gen2_ChC004.k14_86)) (.split 3 (.leaf _ C4.Cert.Gen2_ChC004.k14_87) (.leaf _ C4.Cert.Gen2_ChC004.k14_88))) (.split 1 (.leaf _ C4.Cert.Gen2_ChC004.k14_89) (.leaf _ C4.Cert.Gen2_ChC004.k14_90))))) (.split 3 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC004.k14_91) (.leaf _ C4.Cert.Gen2_ChC004.k14_92)) (.leaf _ C4.Cert.Gen2_ChC004.k14_93)) (.split 1 (.leaf _ C4.Cert.Gen2_ChC005.k14_94) (.leaf _ C4.Cert.Gen2_ChC005.k14_95)))) (.split 1 (.split 3 (.leaf _ C4.Cert.Gen2_ChC005.k14_96) (.leaf _ C4.Cert.Gen2_ChC005.k14_97)) (.split 3 (.split 3 (.leaf _ C4.Cert.Gen2_ChC005.k14_98) (.leaf _ C4.Cert.Gen2_ChC005.k14_99)) (.leaf _ C4.Cert.Gen2_ChC005.k14_100))))) (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChC005.k14_101) (.split 1 (.leaf _ C4.Cert.Gen2_ChC005.k14_102) (.split 2 (.leaf _ C4.Cert.Gen2_ChC005.k14_103) (.split 3 (.leaf _ C4.Cert.Gen2_ChC005.k14_104) (.leaf _ C4.Cert.Gen2_ChC005.k14_105))))) (.split 3 (.split 3 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC005.k14_106) (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC005.k14_107) (.leaf _ C4.Cert.Gen2_ChC005.k14_108)) (.split 1 (.leaf _ C4.Cert.Gen2_ChC005.k14_109) (.leaf _ C4.Cert.Gen2_ChC005.k14_110)))) (.split 2 (.leaf _ C4.Cert.Gen2_ChC005.k14_111) (.split 3 (.split 1 (.leaf _ C4.Cert.Gen2_ChC005.k14_112) (.leaf _ C4.Cert.Gen2_ChC005.k14_113)) (.split 1 (.leaf _ C4.Cert.Gen2_ChC005.k14_114) (.leaf _ C4.Cert.Gen2_ChC005.k14_115))))) (.split 3 (.split 3 (.split 2 (.leaf _ C4.Cert.Gen2_ChC005.k14_116) (.leaf _ C4.Cert.Gen2_ChC005.k14_117)) (.leaf _ C4.Cert.Gen2_ChC005.k14_118)) (.split 3 (.leaf _ C4.Cert.Gen2_ChC005.k14_119) (.leaf _ C4.Cert.Gen2_ChC005.k14_120)))) (.split 1 (.split 3 (.split 3 (.leaf _ C4.Cert.Gen2_ChC005.k14_121) (.leaf _ C4.Cert.Gen2_ChC005.k14_122)) (.leaf _ C4.Cert.Gen2_ChC005.k14_123)) (.split 2 (.split 3 (.leaf _ C4.Cert.Gen2_ChC006.k14_124) (.leaf _ C4.Cert.Gen2_ChC006.k14_125)) (.split 3 (.leaf _ C4.Cert.Gen2_ChC006.k14_126) (.leaf _ C4.Cert.Gen2_ChC006.k14_127)))))))))

end C4.Cert.Gen2_ChC007
