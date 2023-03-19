include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "ccom.mm"
include "ssbr.mm"
include "anim2d.mm"
include "eximdv.mm"
include "ssopab2dv.mm"
include "df-co.mm"
include "3sstr4g.mm"

theorem coss1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ B -> ( A o. C ) C_ ( B o. C ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    vy
    cv
    #
    cC
    wbr
    #
    @1
    vz
    cv
    #
    cA
    wbr
    #
    wa
    #
    vy
    wex
    #
    vx
    vz
    copab
    @2
    @1
    @3
    cB
    wbr
    #
    wa
    #
    vy
    wex
    #
    vx
    vz
    copab
    cA
    cC
    ccom
    cB
    cC
    ccom
    @0
    @6
    @9
    vx
    vz
    @0
    @5
    @8
    vy
    @0
    @4
    @7
    @2
    cA
    cB
    @1
    @3
    ssbr
    anim2d
    eximdv
    ssopab2dv
    vx
    vz
    vy
    cA
    cC
    df-co
    vx
    vz
    vy
    cB
    cC
    df-co
    3sstr4g
end
