include "ckq.mm"
include "cfv.mm"
include "chmph.mm"
include "wbr.mm"
include "ct1.mm"
include "wcel.mm"
include "ct0.mm"
include "t1t0.mm"
include "kqhmph.mm"
include "sylib.mm"
include "t1hmph.mm"
include "mpcom.mm"

theorem t1r0
  let cJ: class J


  assert |- ( J e. Fre -> ( KQ ` J ) e. Fre )

  proof
    cJ
    cJ
    ckq
    cfv
    #
    chmph
    wbr
    #
    cJ
    ct1
    wcel
    #
    @0
    ct1
    wcel
    @2
    cJ
    ct0
    wcel
    @1
    cJ
    t1t0
    cJ
    kqhmph
    sylib
    cJ
    @0
    t1hmph
    mpcom
end
