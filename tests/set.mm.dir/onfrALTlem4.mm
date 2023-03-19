include "wel.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wsbc.mm"
include "sbcan.mm"
include "sbcel1v.mm"
include "csb.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "sbceqg.mm"
include "ax-mp.mm"
include "csbin.mm"
include "csbconstg.mm"
include "csbvarg.mm"
include "ineq12i.mm"
include "eqtri.mm"
include "csb0.mm"
include "eqeq12i.mm"
include "bitri.mm"
include "anbi12i.mm"

theorem onfrALTlem4
  let vx: setvar x
  let vy: setvar y
  let va: setvar a

  disjoint a x
  assert |- ( [. y / x ]. ( x e. a /\ ( a i^i x ) = (/) ) <-> ( y e. a /\ ( a i^i y ) = (/) ) )

  proof
    vx
    va
    wel
    #
    va
    cv
    #
    vx
    cv
    #
    cin
    #
    c0
    wceq
    #
    wa
    vx
    vy
    cv
    #
    wsbc
    @0
    vx
    @5
    wsbc
    #
    @4
    vx
    @5
    wsbc
    #
    wa
    vy
    va
    wel
    #
    @1
    @5
    cin
    #
    c0
    wceq
    #
    wa
    @0
    @4
    vx
    @5
    sbcan
    @6
    @8
    @7
    @10
    vx
    @5
    @1
    sbcel1v
    @7
    vx
    @5
    @3
    csb
    #
    vx
    @5
    c0
    csb
    #
    wceq
    #
    @10
    @5
    cvv
    wcel
    #
    @7
    @13
    wb
    vy
    vex
    #
    vx
    @5
    @3
    c0
    cvv
    sbceqg
    ax-mp
    @11
    @9
    @12
    c0
    @11
    vx
    @5
    @1
    csb
    #
    vx
    @5
    @2
    csb
    #
    cin
    @9
    vx
    @5
    @1
    @2
    csbin
    @16
    @1
    @17
    @5
    @14
    @16
    @1
    wceq
    @15
    vx
    @5
    @1
    cvv
    csbconstg
    ax-mp
    @14
    @17
    @5
    wceq
    @15
    vx
    @5
    cvv
    csbvarg
    ax-mp
    ineq12i
    eqtri
    vx
    @5
    csb0
    eqeq12i
    bitri
    anbi12i
    bitri
end
