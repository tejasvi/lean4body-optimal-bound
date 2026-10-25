module

public import C4.Cap2
public import C4.Kits
public import C4Cert.Gen2_Cover
public import C4Cert.CornerCap

/-!
# The midpoint test at every central configuration of the half `a ≤ 1`

`sharp_cap_of_covers` (`C4/Cap2.lean`) assembles `SharpCapN` from the soundness of the Taylor-model
modes (`C4/Kits.lean`), the four certified covers of the direct and chart regions
(`C4Cert/Gen2_Cover.lean`) and the corner theorem (`C4Cert/CornerCap.lean`).
-/

@[expose] public section

namespace C4

/-- the normalized midpoint test is positive at every CC with `a ≤ 1` -/
theorem sharp_cap : SharpCapN :=
  sharp_cap_of_covers (dirModeTFM_sound tfKitsM) rfl (chModeTFM_sound 7 tfKitsM) rfl rfl
    dir2Cover chACover chBCover chCCover
    CTF.corner_cap

end C4
