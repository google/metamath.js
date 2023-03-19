include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "cabl.mm"
include "c0.mm"
include "wne.mm"
include "vex.mm"
include "eqid.mm"
include "abl1.mm"
include "ne0i.mm"
include "mp2b.mm"

theorem abln0
  let vi: setvar i


  assert |- Abel =/= (/)

  proof
    vi
    cv
    #
    cvv
    wcel
    cnx
    cbs
    cfv
    @0
    csn
    cop
    cnx
    cplusg
    cfv
    @0
    @0
    cop
    @0
    cop
    csn
    cop
    cpr
    #
    cabl
    wcel
    cabl
    c0
    wne
    vi
    vex
    @0
    @1
    cvv
    @1
    eqid
    abl1
    cabl
    @1
    ne0i
    mp2b
end
