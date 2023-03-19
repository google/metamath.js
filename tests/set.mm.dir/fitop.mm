include "ctop.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "cfi.mm"
include "cfv.mm"
include "wceq.mm"
include "inopn.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "inficl.mm"
include "mpbid.mm"

theorem fitop
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( J e. Top -> ( fi ` J ) = J )

  proof
    cJ
    ctop
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    cJ
    wcel
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    cJ
    cfi
    cfv
    cJ
    wceq
    @0
    @3
    vx
    vy
    cJ
    cJ
    @0
    @1
    cJ
    wcel
    @2
    cJ
    wcel
    @3
    @1
    @2
    cJ
    inopn
    3expib
    ralrimivv
    vx
    vy
    cJ
    ctop
    inficl
    mpbid
end
