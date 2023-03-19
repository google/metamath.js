include "c0.mm"
include "cnq.mm"
include "wcel.mm"
include "cnpi.mm"
include "cxp.mm"
include "0nelxp.mm"
include "cv.mm"
include "ceq.mm"
include "wbr.mm"
include "c2nd.mm"
include "cfv.mm"
include "clti.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "df-nq.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "mto.mm"

theorem 0nnq
  let vx: setvar x
  let vy: setvar y


  assert |- -. (/) e. Q.

  proof
    c0
    cnq
    wcel
    c0
    cnpi
    cnpi
    cxp
    #
    wcel
    cnpi
    cnpi
    0nelxp
    cnq
    @0
    c0
    cnq
    vy
    cv
    #
    vx
    cv
    #
    ceq
    wbr
    @2
    c2nd
    cfv
    @1
    c2nd
    cfv
    clti
    wbr
    wn
    wi
    vx
    @0
    wral
    #
    vy
    @0
    crab
    @0
    vy
    vx
    df-nq
    @3
    vy
    @0
    ssrab2
    eqsstri
    sseli
    mto
end
