include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "cfi.mm"
include "wceq.mm"
include "filin.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "inficl.mm"
include "mpbid.mm"

theorem filfi
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. ( Fil ` X ) -> ( fi ` F ) = F )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    cF
    wcel
    #
    vy
    cF
    wral
    vx
    cF
    wral
    cF
    cfi
    cfv
    cF
    wceq
    @1
    @4
    vx
    vy
    cF
    cF
    @1
    @2
    cF
    wcel
    @3
    cF
    wcel
    @4
    @2
    @3
    cF
    cX
    filin
    3expib
    ralrimivv
    vx
    vy
    cF
    @0
    inficl
    mpbid
end
