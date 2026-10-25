module

public import C4.SearchSound2
public import C4.TFSound
public import C4.TFSoundF4

/-!
# The soundness of the Taylor-model kits

`TFSoundK` (`C4/SearchSound2.lean`) collects what the Taylor-model leaf needs from a model type.
The lemmas of `C4/TFSound.lean` give it for the test model `TF.W4`, those of `C4/TFSoundF4.lean`
for the Newton model `TF.F4`, so the Taylor-model modes `dirModeTFM` and `chModeTFM k` are sound
(`dirModeTFM_sound`, `chModeTFM_sound`).
-/

@[expose] public section

namespace C4

/-- the test model `TF.W4` satisfies what the Taylor-model leaf needs -/
theorem soundW4 : TFSoundK kitW4 TF.W4.Enc where
  ops := TF.W4.ops_sound
  var0 := TF.W4.var0_enc
  var1 := TF.W4.var1_enc
  var2 := TF.W4.var2_enc
  var3 := TF.W4.var3_enc
  ptB := TF.W4.ptB_enc
  posT := TF.W4.posT_spec
  newtOK := TF.W4.newtOK_spec

/-- the Newton model `TF.F4` satisfies what the Taylor-model leaf needs -/
theorem soundF4 : TFSoundK kitF4 TF.F4.Enc where
  ops := TF.F4.ops_sound
  var0 := TF.F4.var0_enc
  var1 := TF.F4.var1_enc
  var2 := TF.F4.var2_enc
  var3 := TF.F4.var3_enc
  ptB := TF.F4.ptB_enc
  posT := TF.F4.posT_spec
  newtOK := TF.F4.newtOK_spec

/-- the W4 + F4 kits of the Taylor-model modes `dirModeTFM` and `chModeTFM k` -/
theorem tfKitsM : TFKitsM TF.W4.Enc TF.F4.Enc := ⟨soundW4, soundF4⟩

end C4
