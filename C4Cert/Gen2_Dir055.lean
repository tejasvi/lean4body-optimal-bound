module

public import C4Check

public section

/-! Pieces of cell `22` of the direct root grid: `decide +kernel` checks that `checkBoxH2` succeeds on
each piece with its hint; the cell is assembled in a later module. -/

set_option Elab.async false

namespace C4.Cert.Gen2_Dir055

theorem k22_112 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 22) 1).2 2).2 3).2 1).2 2).1 3).2 2).1
      37622375452771364667859539015743034225783638888162207776853781499529517503574815465524810456033403803912722476456056).isSome = true := by
  decide +kernel

theorem k22_113 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 22) 1).2 2).2 3).2 1).2 2).1 3).2 2).2
      7859905039163072400130708751424993537709579179144624899537288646085238840491044844666101582364503542403666589688600).isSome = true := by
  decide +kernel

theorem k22_114 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 22) 1).2 2).2 3).2 1).2 2).2 3).1
      219584280922133630713139965341445872154589804288010908025327539100439462592499645126483873184581228000630638628755304798171946196799210289988803085872566314250226932214791942092421828835825415150131122919900234602053972611777009951266).isSome = true := by
  decide +kernel

theorem k22_115 : (checkBoxH2 dirModeTFM depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dir2CellBox 22) 1).2 2).2 3).2 1).2 2).2 3).2
      23890148532867726349860360064874045633500247692297579306758870958619273254614914872979688210470626186080369567812379885484132013677990828694500421564776074931680911836873551978905947761710819115782989770717022468305979958791184752340066).isSome = true := by
  decide +kernel

end C4.Cert.Gen2_Dir055
