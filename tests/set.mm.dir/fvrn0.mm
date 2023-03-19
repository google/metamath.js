include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "crn.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "id.mm"
include "ssun2.mm"
include "0ex.mm"
include "snid.mm"
include "sselii.mm"
include "syl6eqel.mm"
include "wn.mm"
include "ssun1.mm"
include "cvv.mm"
include "wbr.mm"
include "fvprc.mm"
include "con1i.mm"
include "fvexd.mm"
include "fvbr0.mm"
include "ori.mm"
include "brelrng.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "pm2.61i.mm"

theorem fvrn0
  let cF: class F
  let cX: class X


  assert |- ( F ` X ) e. ( ran F u. { (/) } )

  proof
    cX
    cF
    cfv
    #
    c0
    wceq
    #
    @0
    cF
    crn
    #
    c0
    csn
    #
    cun
    #
    wcel
    @1
    @0
    c0
    @4
    @1
    id
    @3
    @4
    c0
    @3
    @2
    ssun2
    c0
    0ex
    snid
    sselii
    syl6eqel
    @1
    wn
    #
    @2
    @4
    @0
    @2
    @3
    ssun1
    @5
    cX
    cvv
    wcel
    #
    @0
    cvv
    wcel
    cX
    @0
    cF
    wbr
    #
    @0
    @2
    wcel
    @6
    @1
    cX
    cF
    fvprc
    con1i
    @5
    cX
    cF
    fvexd
    @7
    @1
    @7
    @1
    cF
    cX
    fvbr0
    ori
    con1i
    cX
    @0
    cF
    cvv
    cvv
    brelrng
    syl3anc
    sseldi
    pm2.61i
end
