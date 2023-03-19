include "ccph.mm"
include "wcel.mm"
include "cnlm.mm"
include "cngp.mm"
include "cphnlm.mm"
include "nlmngp.mm"
include "syl.mm"

theorem cphngp
  let cW: class W


  assert |- ( W e. CPreHil -> W e. NrmGrp )

  proof
    cW
    ccph
    wcel
    cW
    cnlm
    wcel
    cW
    cngp
    wcel
    cW
    cphnlm
    cW
    nlmngp
    syl
end
