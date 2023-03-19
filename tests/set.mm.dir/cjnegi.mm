include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjneg.mm"
include "ax-mp.mm"

theorem cjnegi
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( * ` -u A ) = -u ( * ` A )

  proof
    cA
    cc
    wcel
    cA
    cneg
    ccj
    cfv
    cA
    ccj
    cfv
    cneg
    wceq
    recl.1
    cA
    cjneg
    ax-mp
end
