include "cbn.mm"
include "wcel.mm"
include "cnlm.mm"
include "clmod.mm"
include "bnnlm.mm"
include "nlmlmod.mm"
include "syl.mm"

theorem bnlmod
  let cW: class W


  assert |- ( W e. Ban -> W e. LMod )

  proof
    cW
    cbn
    wcel
    cW
    cnlm
    wcel
    cW
    clmod
    wcel
    cW
    bnnlm
    cW
    nlmlmod
    syl
end
