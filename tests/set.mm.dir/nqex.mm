include "cv.mm"
include "ceq.mm"
include "wbr.mm"
include "c2nd.mm"
include "cfv.mm"
include "clti.mm"
include "wn.mm"
include "wi.mm"
include "cnpi.mm"
include "cxp.mm"
include "wral.mm"
include "cnq.mm"
include "df-nq.mm"
include "niex.mm"
include "xpex.mm"
include "rabex2.mm"

theorem nqex
  let vx: setvar x
  let vy: setvar y


  assert |- Q. e. _V

  proof
    vy
    cv
    #
    vx
    cv
    #
    ceq
    wbr
    @1
    c2nd
    cfv
    @0
    c2nd
    cfv
    clti
    wbr
    wn
    wi
    vx
    cnpi
    cnpi
    cxp
    #
    wral
    vy
    @2
    cnq
    vy
    vx
    df-nq
    cnpi
    cnpi
    niex
    niex
    xpex
    rabex2
end
