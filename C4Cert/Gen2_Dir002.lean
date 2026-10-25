module

public import C4Check

public section

/-! Pieces of cell `1` of the direct root grid: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_Dir002

theorem k1_64 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).2 2).2 3).2 1).2 2).1 3).2
      1476012631446709061546920715177609968089246389798722575648868742173063271798452110785091919893235828665999406712152).isSome = true := by
  decide +kernel

theorem k1_65 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).2 2).2 3).2 1).2 2).2 3).1
      249082271380435253779210842332952062836099662742327822755474714810408452232770709208831814131832625601454031746516755736438724681955121195065721966362521843024009490271642345949385139268392412753719025153573577359068330482007796088867).isSome = true := by
  decide +kernel

theorem k1_66 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 1) 1).2 2).2 3).2 1).2 2).2 3).2 1).2 2).2 3).2
      228622984945185408222359684794366097731334141679270503759092741488540237807802807195905628594271001045411481161997631327499266668930182195076021953202366635077531151739234216874949402176128277846834950974856635891066802212197423427826533730).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_Dir002
