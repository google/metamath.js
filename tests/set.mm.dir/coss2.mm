include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "ccom.mm"
include "ssbr.mm"
include "anim1d.mm"
include "eximdv.mm"
include "ssopab2dv.mm"
include "df-co.mm"
include "3sstr4g.mm"

theorem coss2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ B -> ( C o. A ) C_ ( C o. B ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    @2
    vz
    cv
    cC
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
    @1
    @2
    cB
    wbr
    #
    @4
    wa
    #
    vy
    wex
    #
    vx
    vz
    copab
    cC
    cA
    ccom
    cC
    cB
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
    @3
    @7
    @4
    cA
    cB
    @1
    @2
    ssbr
    anim1d
    eximdv
    ssopab2dv
    vx
    vz
    vy
    cC
    cA
    df-co
    vx
    vz
    vy
    cC
    cB
    df-co
    3sstr4g
end
