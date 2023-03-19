include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wpo.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syld.mm"
include "df-po.mm"
include "3imtr4g.mm"

theorem poss
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ B -> ( R Po B -> R Po A ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    @1
    cR
    wbr
    wn
    @1
    vy
    cv
    #
    cR
    wbr
    @2
    vz
    cv
    #
    cR
    wbr
    wa
    @1
    @3
    cR
    wbr
    wi
    wa
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @4
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    cB
    cR
    wpo
    cA
    cR
    wpo
    @0
    @7
    @6
    vx
    cA
    wral
    @10
    @6
    vx
    cA
    cB
    ssralv
    @0
    @6
    @9
    vx
    cA
    @0
    @6
    @5
    vy
    cA
    wral
    @9
    @5
    vy
    cA
    cB
    ssralv
    @0
    @5
    @8
    vy
    cA
    @4
    vz
    cA
    cB
    ssralv
    ralimdv
    syld
    ralimdv
    syld
    vx
    vy
    vz
    cB
    cR
    df-po
    vx
    vy
    vz
    cA
    cR
    df-po
    3imtr4g
end
