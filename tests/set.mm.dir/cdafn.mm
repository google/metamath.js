include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "ccda.mm"
include "df-cda.mm"
include "vex.mm"
include "snex.mm"
include "xpex.mm"
include "unex.mm"
include "fnmpt2i.mm"

theorem cdafn
  let vx: setvar x
  let vy: setvar y


  assert |- +c Fn ( _V X. _V )

  proof
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    c0
    csn
    #
    cxp
    #
    vy
    cv
    #
    c1o
    csn
    #
    cxp
    #
    cun
    ccda
    vx
    vy
    df-cda
    @2
    @5
    @0
    @1
    vx
    vex
    c0
    snex
    xpex
    @3
    @4
    vy
    vex
    c1o
    snex
    xpex
    unex
    fnmpt2i
end
