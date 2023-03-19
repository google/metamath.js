include "wel.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "sbcangOLD.mm"
include "e0a.mm"
include "sbcel1gvOLD.mm"
include "csb.mm"
include "sbceqg.mm"
include "csbingOLD.mm"
include "csbconstg.mm"
include "csbvarg.mm"
include "ineq12i.mm"
include "eqtri.mm"
include "eqeq12i.mm"
include "bitri.mm"
include "anbi12i.mm"

theorem onfrALTlem4VD
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
    #
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
    #
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
    @5
    cvv
    wcel
    #
    @6
    @9
    wb
    vy
    vex
    #
    @0
    @4
    vx
    @5
    cvv
    sbcangOLD
    e0a
    @7
    @10
    @8
    @12
    @13
    @7
    @10
    wb
    @14
    vx
    @5
    @1
    cvv
    sbcel1gvOLD
    e0a
    @8
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
    @12
    @13
    @8
    @17
    wb
    @14
    vx
    @5
    @3
    c0
    cvv
    sbceqg
    e0a
    @15
    @11
    @16
    c0
    @15
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
    #
    @11
    @13
    @15
    @20
    wceq
    @14
    vx
    @5
    cvv
    @1
    @2
    csbingOLD
    e0a
    @18
    @1
    @19
    @5
    @13
    @18
    @1
    wceq
    @14
    vx
    @5
    @1
    cvv
    csbconstg
    e0a
    @13
    @19
    @5
    wceq
    @14
    vx
    @5
    cvv
    csbvarg
    e0a
    ineq12i
    eqtri
    @13
    @16
    c0
    wceq
    @14
    vx
    @5
    c0
    cvv
    csbconstg
    e0a
    eqeq12i
    bitri
    anbi12i
    bitri
end
