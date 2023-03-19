include "cv.mm"
include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wcel.mm"
include "cin.mm"
include "wceq.mm"
include "wex.mm"
include "wrex.mm"
include "wsb.mm"
include "idn2.mm"
include "19.8a.mm"
include "e2.mm"
include "cbvexsv.mm"
include "biimpi.mm"
include "wb.mm"
include "wal.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "onfrALTlem4.mm"
include "bitri.mm"
include "ax-gen.mm"
include "exbi.mm"
include "e0a.mm"
include "e2bi.mm"
include "df-rex.mm"
include "e2bir.mm"

theorem onfrALTlem1VD
  let vx: setvar x
  let vy: setvar y
  let va: setvar a

  disjoint a x
  disjoint a y
  disjoint x y
  assert |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a /\ ( a i^i x ) = (/) ) ->. E. y e. a ( a i^i y ) = (/) ).

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
    cv
    #
    @0
    wcel
    @0
    @2
    cin
    c0
    wceq
    wa
    #
    vy
    cv
    #
    @0
    wcel
    @0
    @4
    cin
    c0
    wceq
    #
    wa
    #
    vy
    wex
    #
    @5
    vy
    @0
    wrex
    @1
    @3
    @3
    vx
    vy
    wsb
    #
    vy
    wex
    #
    @7
    @1
    @3
    @3
    vx
    wex
    #
    @9
    @1
    @3
    @3
    @10
    @1
    @3
    idn2
    @3
    vx
    19.8a
    e2
    @10
    @9
    @3
    vx
    vy
    cbvexsv
    biimpi
    e2
    @8
    @6
    wb
    #
    vy
    wal
    @9
    @7
    wb
    @11
    vy
    @8
    @3
    vx
    @4
    wsbc
    @6
    @3
    vx
    vy
    sbsbc
    vx
    vy
    va
    onfrALTlem4
    bitri
    ax-gen
    @8
    @6
    vy
    exbi
    e0a
    e2bi
    @5
    vy
    @0
    df-rex
    e2bir
end
