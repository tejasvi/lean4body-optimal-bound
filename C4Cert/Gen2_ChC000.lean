module

public import C4Check

public section

/-! Cells `0 ≤ n < 10` of the chart root grid C: `decide +kernel` checks that `checkBoxH2` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Gen2_ChC000

theorem c0 : allCells (cellOK (chModeTFM 7) chCCellBox) 0 4 [
    0, 0, 0, 0] = true := by
  decide +kernel

theorem k4_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (chCCellBox 4) 1).1
      3170).isSome = true := by
  decide +kernel

theorem k4_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chCCellBox 4) 1).2 1).1
      21661485859779393203045766814584152513376850843870628118324054496467542415104326348221072071938830008771459796279805052727624066).isSome = true := by
  decide +kernel

theorem k4_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chCCellBox 4) 1).2 1).2
      874009996786400866627941652618179373592561719446630833662413946237107761124921825661652048066260615986020862371196992437537839377440279682592922973328310787321669340567399467824540548100483537309095548356952661192338776601218749703258930269438211).isSome = true := by
  decide +kernel

theorem k5_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (chCCellBox 5) 1).1
      8445961).isSome = true := by
  decide +kernel

theorem k5_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 5) 1).2 1).1 3).1 2).1
      10329001359627709928709250764551127011188128386174122285614519529301033727035993001188846456775671919007008481026654386984).isSome = true := by
  decide +kernel

theorem k5_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 5) 1).2 1).1 3).1 2).2
      472644729993898228431739804893102788247547450800547301049463464100288370790974670208168634488456723007444199116723171726224220400328324877910725490817133649262876629735034690403870513921029151605720363109135088291867722388084258931105).isSome = true := by
  decide +kernel

theorem k5_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chCCellBox 5) 1).2 1).1 3).2
      20657999741539600206194176230277500204951912444600301511478037786647391723463310454033166321500286918513565835978643769832).isSome = true := by
  decide +kernel

theorem k5_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 5) 1).2 1).2 2).1 3).1
      5164736260931457255376984898214166825505354951693256646177846475995565441469864267019494040097348935952750864612873733123).isSome = true := by
  decide +kernel

theorem k5_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 5) 1).2 1).2 2).1 3).2
      454014511608841358480805859695131323195315552457675504288848985778140389352592232608590375852562866849052593968604324266248709235147542256203634411159580987238944345070211795907712087764036591735035648048353456369808777867108447598753).isSome = true := by
  decide +kernel

theorem k5_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 5) 1).2 1).2 2).2 3).1
      26673278992610629035589287992029276640650448818591818573130212038051190705188021957487163084212969479602670651011261667549601180037741656905653941467382614813519201204518786774124090160470154620928783352528158624229562050008602743201892123809).isSome = true := by
  decide +kernel

theorem k5_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 5) 1).2 1).2 2).2 3).2
      10329000210326123278951939427513748189017153281975261390265855560576599991009256274733619553918048976510957406307537367880).isSome = true := by
  decide +kernel

theorem c3 : allCells (cellOK (chModeTFM 7) chCCellBox) 6 9 [
    0, 0, 98] = true := by
  decide +kernel

theorem k9_0 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (chCCellBox 9) 1).1 1).1
      527502463072259848832349881428976807283961579004186756506233095661302929997986736562135672685044028439194063122661252275232874311811273282468359943052200190179244505646947325642643115420264066991091016685413834603410409950189540510793659857934).isSome = true := by
  decide +kernel

theorem k9_1 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chCCellBox 9) 1).1 1).2 2).1
      3).isSome = true := by
  decide +kernel

theorem k9_2 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 9) 1).1 1).2 2).2 3).1
      10329058631622935387641210261423739263876308472911532714352416717600478086814764097879849515774774109851682704991361300739).isSome = true := by
  decide +kernel

theorem k9_3 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 9) 1).1 1).2 2).2 3).2
      10802421125731465623606186060682429410529644538303139268233193821640838840175790255445469341482496064825984915606904955631877283789702633791953501564031947909580180890220092441024985325422176197001623323105915184968594318193511452992523).isSome = true := by
  decide +kernel

theorem k9_4 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chCCellBox 9) 1).2 1).1 2).1
      99).isSome = true := by
  decide +kernel

theorem k9_5 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 9) 1).2 1).1 2).2 3).1
      1322112174056395948051586958674420505851467990535269946969675945258618233749083779032335321398017144642567435298875518686211).isSome = true := by
  decide +kernel

theorem k9_6 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 9) 1).2 1).1 2).2 3).2
      46389241441882370835729054228179588256542592948925194370962209149820893639978739522677548254966683448529449652199782809862088757561324289356395616314693751651303947520437939792168624250194429982262540206157002372773096292004275308875787).isSome = true := by
  decide +kernel

theorem k9_7 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (chCCellBox 9) 1).2 1).2 2).1
      165265883966273624798529705406400002302818273409788426092788990921057900372406304194581194195050209324812918053529862316131).isSome = true := by
  decide +kernel

theorem k9_8 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (chCCellBox 9) 1).2 1).2 2).2 3).1
      2736183679813668058905521626037208856872412206080592489723402131293946023653690239437594910328320405369174281322755).isSome = true := by
  decide +kernel

theorem k9_9 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 9) 1).2 1).2 2).2 3).2 3).1
      10088886175190608267857915794614033933191556802758505429785604371791658287104248420767562417510369620195349426642695208).isSome = true := by
  decide +kernel

theorem k9_10 : (checkBoxH2 (chModeTFM 7) depth (splitBox (splitBox (splitBox (splitBox (splitBox (chCCellBox 9) 1).2 1).2 2).2 3).2 3).2
      178292986210040501492024793438830840576551073055601238730990979922158533947030975747472732788787961454306051891496).isSome = true := by
  decide +kernel

theorem cover : Cover2 (chModeTFM 7) chCCellBox 0 10 :=
  (Cover2.cells c0).trans <|
  (Cover2.one (box := chCCellBox) (n := 4)
      (.split 1 (.leaf _ k4_0) (.split 1 (.leaf _ k4_1) (.leaf _ k4_2)))).trans <|
  (Cover2.one (box := chCCellBox) (n := 5)
      (.split 1 (.leaf _ k5_0) (.split 1 (.split 3 (.split 2 (.leaf _ k5_1) (.leaf _ k5_2)) (.leaf _ k5_3)) (.split 2 (.split 3 (.leaf _ k5_4) (.leaf _ k5_5)) (.split 3 (.leaf _ k5_6) (.leaf _ k5_7)))))).trans <|
  (Cover2.cells c3).trans <|
  (Cover2.one (box := chCCellBox) (n := 9)
      (.split 1 (.split 1 (.leaf _ k9_0) (.split 2 (.leaf _ k9_1) (.split 3 (.leaf _ k9_2) (.leaf _ k9_3)))) (.split 1 (.split 2 (.leaf _ k9_4) (.split 3 (.leaf _ k9_5) (.leaf _ k9_6))) (.split 2 (.leaf _ k9_7) (.split 3 (.leaf _ k9_8) (.split 3 (.leaf _ k9_9) (.leaf _ k9_10)))))))

end C4.Cert.Gen2_ChC000
