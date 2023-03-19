include "cale.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "com.mm"
include "cun.mm"
include "cv.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cab.mm"
include "cardprc.mm"
include "neli.mm"
include "cardnum.mm"
include "eleq1i.mm"
include "mtbi.mm"
include "omex.mm"
include "unexg.mm"
include "mpan.mm"
include "mto.mm"

theorem alephprc
  let vx: setvar x


  assert |- -. ran aleph e. _V

  proof
    cale
    crn
    #
    cvv
    wcel
    #
    com
    @0
    cun
    #
    cvv
    wcel
    #
    vx
    cv
    #
    ccrd
    cfv
    @4
    wceq
    vx
    cab
    #
    cvv
    wcel
    @3
    @5
    cvv
    vx
    cardprc
    neli
    @5
    @2
    cvv
    vx
    cardnum
    eleq1i
    mtbi
    com
    cvv
    wcel
    @1
    @3
    omex
    com
    @0
    cvv
    cvv
    unexg
    mpan
    mto
end
