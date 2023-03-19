include "cv.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cab.mm"
include "cvv.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "cbvabv.mm"
include "cardprclem.mm"
include "nelir.mm"

theorem cardprc
  let vx: setvar x
  let vy: setvar y


  assert |- { x | ( card ` x ) = x } e/ _V

  proof
    vx
    cv
    #
    ccrd
    cfv
    #
    @0
    wceq
    #
    vx
    cab
    #
    cvv
    vy
    @3
    @2
    vy
    cv
    #
    ccrd
    cfv
    #
    @4
    wceq
    vx
    vy
    vx
    vy
    weq
    #
    @1
    @5
    @0
    @4
    @0
    @4
    ccrd
    fveq2
    @6
    id
    eqeq12d
    cbvabv
    cardprclem
    nelir
end
