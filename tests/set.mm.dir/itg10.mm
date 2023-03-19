include "cr.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "citg1.mm"
include "cfv.mm"
include "crn.mm"
include "cdif.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "c0.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "i1f0.mm"
include "itg1val.mm"
include "ax-mp.mm"
include "wss.mm"
include "rnxpss.mm"
include "ssdif0.mm"
include "mpbi.mm"
include "sumeq1i.mm"
include "sum0.mm"
include "3eqtri.mm"

theorem itg10
  let vx: setvar x


  assert |- ( S.1 ` ( RR X. { 0 } ) ) = 0

  proof
    cr
    cc0
    csn
    #
    cxp
    #
    citg1
    cfv
    #
    @1
    crn
    #
    @0
    cdif
    #
    vx
    cv
    #
    @1
    ccnv
    @5
    csn
    cima
    cvol
    cfv
    cmul
    co
    #
    vx
    csu
    #
    c0
    @6
    vx
    csu
    cc0
    @1
    citg1
    cdm
    wcel
    @2
    @7
    wceq
    i1f0
    vx
    @1
    itg1val
    ax-mp
    @4
    c0
    @6
    vx
    @3
    @0
    wss
    @4
    c0
    wceq
    cr
    @0
    rnxpss
    @3
    @0
    ssdif0
    mpbi
    sumeq1i
    @6
    vx
    sum0
    3eqtri
end
