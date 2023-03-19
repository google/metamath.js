include "cv.mm"
include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wel.mm"
include "cin.mm"
include "wceq.mm"
include "wex.mm"
include "wrex.mm"
include "wsb.mm"
include "wi.mm"
include "19.8a.mm"
include "a1i.mm"
include "cbvexsv.mm"
include "syl6ib.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "onfrALTlem4.mm"
include "bitri.mm"
include "exbii.mm"
include "df-rex.mm"
include "syl6ibr.mm"

theorem onfrALTlem1
  let vx: setvar x
  let vy: setvar y
  let va: setvar a

  disjoint a x
  disjoint a y
  disjoint x y
  assert |- ( ( a C_ On /\ a =/= (/) ) -> ( ( x e. a /\ ( a i^i x ) = (/) ) -> E. y e. a ( a i^i y ) = (/) ) )

  proof
    va
    cv
    #
    con0
    wss
    @0
    c0
    wne
    wa
    #
    vx
    va
    wel
    @0
    vx
    cv
    cin
    c0
    wceq
    wa
    #
    vy
    va
    wel
    @0
    vy
    cv
    #
    cin
    c0
    wceq
    #
    wa
    #
    vy
    wex
    #
    @4
    vy
    @0
    wrex
    @1
    @2
    @2
    vx
    vy
    wsb
    #
    vy
    wex
    #
    @6
    @1
    @2
    @2
    vx
    wex
    #
    @8
    @2
    @9
    wi
    @1
    @2
    vx
    19.8a
    a1i
    @2
    vx
    vy
    cbvexsv
    syl6ib
    @7
    @5
    vy
    @7
    @2
    vx
    @3
    wsbc
    @5
    @2
    vx
    vy
    sbsbc
    vx
    vy
    va
    onfrALTlem4
    bitri
    exbii
    syl6ib
    @4
    vy
    @0
    df-rex
    syl6ibr
end
