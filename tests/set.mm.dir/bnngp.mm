include "cbn.mm"
include "wcel.mm"
include "cnlm.mm"
include "cngp.mm"
include "bnnlm.mm"
include "nlmngp.mm"
include "syl.mm"

theorem bnngp
  let cW: class W


  assert |- ( W e. Ban -> W e. NrmGrp )

  proof
    cW
    cbn
    wcel
    cW
    cnlm
    wcel
    cW
    cngp
    wcel
    cW
    bnnlm
    cW
    nlmngp
    syl
end
