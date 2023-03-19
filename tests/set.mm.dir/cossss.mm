include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "ccoss.mm"
include "ssbr.mm"
include "anim12d.mm"
include "eximdv.mm"
include "ssopab2dv.mm"
include "df-coss.mm"
include "3sstr4g.mm"

theorem cossss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ B -> ,~ A C_ ,~ B )

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
    @1
    vz
    cv
    #
    cA
    wbr
    #
    wa
    #
    vx
    wex
    #
    vy
    vz
    copab
    @1
    @2
    cB
    wbr
    #
    @1
    @4
    cB
    wbr
    #
    wa
    #
    vx
    wex
    #
    vy
    vz
    copab
    cA
    ccoss
    cB
    ccoss
    @0
    @7
    @11
    vy
    vz
    @0
    @6
    @10
    vx
    @0
    @3
    @8
    @5
    @9
    cA
    cB
    @1
    @2
    ssbr
    cA
    cB
    @1
    @4
    ssbr
    anim12d
    eximdv
    ssopab2dv
    vy
    vz
    vx
    cA
    df-coss
    vy
    vz
    vx
    cB
    df-coss
    3sstr4g
end
