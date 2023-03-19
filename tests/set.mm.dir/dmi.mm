include "cid.mm"
include "cdm.mm"
include "cvv.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "eqv.mm"
include "wbr.mm"
include "wex.mm"
include "ax6ev.mm"
include "vex.mm"
include "ideq.mm"
include "equcom.mm"
include "bitri.mm"
include "exbii.mm"
include "mpbir.mm"
include "eldm.mm"
include "mpgbir.mm"

theorem dmi
  let vx: setvar x
  let vy: setvar y


  assert |- dom _I = _V

  proof
    cid
    cdm
    #
    cvv
    wceq
    vx
    cv
    #
    @0
    wcel
    #
    vx
    vx
    @0
    eqv
    @2
    @1
    vy
    cv
    #
    cid
    wbr
    #
    vy
    wex
    #
    @5
    @3
    @1
    wceq
    #
    vy
    wex
    vy
    vx
    ax6ev
    @4
    @6
    vy
    @4
    @1
    @3
    wceq
    @6
    @1
    @3
    vy
    vex
    ideq
    vx
    vy
    equcom
    bitri
    exbii
    mpbir
    vy
    @1
    cid
    vx
    vex
    eldm
    mpbir
    mpgbir
end
