include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cuni.mm"
include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "tg1.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "a1i.mm"
include "bastg.mm"
include "unissd.mm"
include "eqssd.mm"

theorem unitg
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C


  assert |- ( B e. V -> U. ( topGen ` B ) = U. B )

  proof
    cB
    cV
    wcel
    #
    cB
    ctg
    cfv
    #
    cuni
    #
    cB
    cuni
    #
    @2
    @3
    wss
    #
    @0
    @1
    @3
    cpw
    #
    wss
    @4
    vx
    @1
    @5
    vx
    cv
    #
    @1
    wcel
    @6
    @3
    wss
    @6
    @5
    wcel
    @6
    cB
    tg1
    vx
    @3
    selpw
    sylibr
    ssriv
    @1
    @3
    sspwuni
    mpbi
    a1i
    @0
    cB
    @1
    cB
    cV
    bastg
    unissd
    eqssd
end
