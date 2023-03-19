include "wrel.mm"
include "ccnv.mm"
include "wceq.mm"
include "relcnv.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "vex.mm"
include "opelcnv.mm"
include "bitri.mm"
include "eqrelriv.mm"
include "mpan.mm"
include "releq.mm"
include "mpbii.mm"
include "impbii.mm"

theorem dfrel2
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( Rel R <-> `' `' R = R )

  proof
    cR
    wrel
    #
    cR
    ccnv
    #
    ccnv
    #
    cR
    wceq
    #
    @2
    wrel
    #
    @0
    @3
    @1
    relcnv
    #
    vx
    vy
    @2
    cR
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @2
    wcel
    @7
    @6
    cop
    @1
    wcel
    @8
    cR
    wcel
    @6
    @7
    @1
    vx
    vex
    #
    vy
    vex
    #
    opelcnv
    @7
    @6
    cR
    @10
    @9
    opelcnv
    bitri
    eqrelriv
    mpan
    @3
    @4
    @0
    @5
    @2
    cR
    releq
    mpbii
    impbii
end
