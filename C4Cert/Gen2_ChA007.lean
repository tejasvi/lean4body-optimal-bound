module

public import C4Check

public section

/-! Pieces of cell `5` of the chart root grid A: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChA007

theorem k5_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).1
      3).isSome = true := by
  decide +kernel

theorem k5_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).1 2).1
      3).isSome = true := by
  decide +kernel

theorem k5_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).1 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k5_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).1 2).2 3).2 1).1 2).1
      626328170833551427848177448004279346078124484099156516780927242748563273953191615923981274878238318806135319765091).isSome = true := by
  decide +kernel

theorem k5_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).1 2).2 3).2 1).1 2).2 3).1
      478854837093050660507494155804534469201136478152597919590213850089776523530985359219388916480589814623152815268862197318672018536238171739193994892553830433642397435286213823872341159621761872622863946967390331544833191512306406235299).isSome = true := by
  decide +kernel

theorem k5_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).1 2).2 3).2 1).1 2).2 3).2
      325155531327701481840520686197333643230706277141946548751806291177471057114328242139581161182296585516052307590557481913682313364906642759861591183287944032353265077240206997242326187004627099400710659686776126026928476752054848911139).isSome = true := by
  decide +kernel

theorem k5_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).1 2).2 3).2 1).2 2).1
      2582269728301954573577397450634680193270227134299832822443308652823537715206362264103016640097120710965432859918435).isSome = true := by
  decide +kernel

theorem k5_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).1
      304972811438737453645216370385411193427056678926240516075680089492773801397204848806085062234665843681161722335928652798781580039481296227304438502013698393951006979055051785532332805448863872074472644992696553578352118748278454190627).isSome = true := by
  decide +kernel

theorem k5_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).1 2).2 3).2 1).2 2).2 3).2
      349995820875316502717859454340637668991614767878660935109289423302819690600276142030565991977526929782278911840905354624813862407137848281367827288003608183602998132990834709854516095367675540804635333469042526774840638521726353051427).isSome = true := by
  decide +kernel

theorem k5_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).1
      3).isSome = true := by
  decide +kernel

theorem k5_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).1
      3).isSome = true := by
  decide +kernel

theorem k5_11 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).2 1).1 2).1
      10790821179457596817334248336265103909074241643781317489095530349308326879775374427080075882076990212976857737986435).isSome = true := by
  decide +kernel

theorem k5_12 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).2 1).1 2).2 3).1
      317392956843339314124200883054846449571572058106245617769049286001551878148315678432583937777645404244729001739876556967301778363099386469664722858709578521714042377225456256863373727361903456664644285201877519290040074885791965184547).isSome = true := by
  decide +kernel

theorem k5_13 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).2 1).1 2).2 3).2 3).1
      501267102944874736722099011140171941780320452740933644130101198035723389019017476534608310118520142942332327304).isSome = true := by
  decide +kernel

theorem k5_14 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).2 1).1 2).2 3).2 3).2
      567026285385122846049388049896191914165721385161496509981980748163929154192477995409174436099106278452702957992).isSome = true := by
  decide +kernel

theorem k5_15 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).2 1).2 2).1
      11252563445445325205356969049527842752265327225594217312303278559847049477309348197661083617562299642670548509655427).isSome = true := by
  decide +kernel

theorem k5_16 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).2 1).2 2).2 3).1
      336023174601239163720404347794593857928325121302250962059618159193743992321110850517496901783716969485532026596369174555446058004497232635624745984884499603601058194177306084283589807407147445603484939698108146635802607842209827264803).isSome = true := by
  decide +kernel

theorem k5_17 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).2 1).2 2).2 3).2 3).1
      538843784664533285257759842285156630155158952587040181407960315982794452697707378973838287525625551722355474920).isSome = true := by
  decide +kernel

theorem k5_18 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).1 3).2 1).2 2).2 3).2 1).2 2).2 3).2 3).2
      313383686530783284013804788566750143197536716837805816104275711542060931631963585864245875680195099261373023816).isSome = true := by
  decide +kernel

theorem k5_19 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).1 2).1
      410726817955548253135296595591729323090308872653457221197636394669277915070068924784749987579034754128286564065252614243).isSome = true := by
  decide +kernel

theorem k5_20 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).1 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k5_21 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).1 2).2 3).2 1).1
      229116476224165572170945837945987933890851719500541574988330287622243516488715020879771092622300893953344492145842787973934290481056504607007432496321370933731867044829506406812876805840265465487503609458076878857794009149300778132873868576616916977038).isSome = true := by
  decide +kernel

theorem k5_22 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 2).1
      2922862178029781758477369165570921141426348569794158366523799240468641557351025402016191938155808316688099201398341987).isSome = true := by
  decide +kernel

theorem k5_23 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).1 2).2 3).2 1).2 2).2
      46001078550717005410509840020843944388997519578152640432532819669099992744920187732457088153800043992736076626133347).isSome = true := by
  decide +kernel

theorem k5_24 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).2 2).1
      217455889946854751477492313891520995785451210191605817785049538044846750839282638675852351119020493718239501581302104465507).isSome = true := by
  decide +kernel

theorem k5_25 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).2 2).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k5_26 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).2 2).2 3).2 1).1 2).1
      3160197699807316432843040026082648126934131769647314300134257242271198924450843121316923567634498583326569005365592419).isSome = true := by
  decide +kernel

theorem k5_27 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).2 2).2 3).2 1).1 2).2
      48463703955820028547485399296187527070839284364041222706089071753354222519301527923200597593499259040620073001681251).isSome = true := by
  decide +kernel

theorem k5_28 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).2 2).2 3).2 1).2 2).1
      3476414191020779622849918280886672677915311925388154927423942426547497952446036146329673389874890669660855221416624483).isSome = true := by
  decide +kernel

theorem k5_29 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).1 1).2 2).2 3).2 1).2 2).2
      203705317428282762897568033098709539700695842800142279441433666463469831026099899648112047555759515518212996186767715).isSome = true := by
  decide +kernel

theorem k5_30 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).1 3).1
      3457165325198394122334450978255756101104386423654245372456010136505830012143256562560007641902008427354499555426).isSome = true := by
  decide +kernel

theorem k5_31 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).1 3).2
      12342520320569191679409219207245050221190400224115619756618367088920152107539499178235552626236912543757953330956069075801697492882080775353365965127779635816250355544475748649254403849562001099756562898635396223718727841149051855426571).isSome = true := by
  decide +kernel

theorem k5_32 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).2 3).1 3).1
      91612976668323683750511653258315942917248839586774220867908196722381973531206732731369369884999259500227041662600).isSome = true := by
  decide +kernel

theorem k5_33 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).2 3).1 3).2
      416719604958294294733208440029724619910131103180471003702444937554899202995553447259129824513418152236759575432).isSome = true := by
  decide +kernel

theorem k5_34 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).2 3).2 3).1
      360354562702879932147472649168413718006753649887949935141294994113428782590311911564339683434589636947956201960).isSome = true := by
  decide +kernel

theorem k5_35 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).1 2).2 3).2 3).2
      350960378573581748046660861660434774367272276086587114018696212009003941710759230404337768667666926463143690696).isSome = true := by
  decide +kernel

theorem k5_36 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).2 2).1 3).1
      3457171043406706828952993561078429073279518926989925222906215002802662391522405503764899343456623068406142345314).isSome = true := by
  decide +kernel

theorem k5_37 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).2 2).1 3).2
      26517015121611969305710309445490488948142890092215142579213087600088055254004235628576752839713127255958115936165806737834615919334279973283554193599675104092072845373214899661400034452283978394679317369645459818860627183460696740679691).isSome = true := by
  decide +kernel

theorem k5_38 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (chACellBox 5) 1).1 2).2 3).2 1).1 2).1 3).1 1).2 2).2 3).1 3).1
      101281926486875649617708041222169257947069172006635829595950927040232264667202326444540758123682137029531795094856).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_ChA007
