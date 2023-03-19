include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "cen.mm"
include "cdom.mm"
include "sdomdom.mm"
include "ccrd.mm"
include "cdm.mm"
include "ondomen.mm"
include "isnum2.mm"
include "sylib.mm"
include "sylan2.mm"
include "ensdomtr.mm"
include "ad2ant2l.mm"
include "wi.mm"
include "sdomel.mm"
include "ad2ant2r.mm"
include "mpd.mm"
include "vex.mm"
include "canth2.mm"
include "ensym.mm"
include "sdomentr.mm"
include "sylancr.mm"
include "ad2antlr.mm"
include "jca.mm"
include "expcom.mm"
include "reximdv2.mm"
include "ex.mm"
include "ralimdv.mm"

theorem inawinalem
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. On -> ( A. x e. A ~P x ~< A -> A. x e. A E. y e. A x ~< y ) )

  proof
    cA
    con0
    wcel
    #
    vx
    cv
    #
    cpw
    #
    cA
    csdm
    wbr
    #
    @1
    vy
    cv
    #
    csdm
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cA
    @0
    @3
    @6
    @0
    @3
    wa
    #
    @4
    @2
    cen
    wbr
    #
    vy
    con0
    wrex
    #
    @6
    @3
    @0
    @2
    cA
    cdom
    wbr
    #
    @9
    @2
    cA
    sdomdom
    @0
    @10
    wa
    @2
    ccrd
    cdm
    wcel
    @9
    cA
    @2
    ondomen
    vy
    @2
    isnum2
    sylib
    sylan2
    @7
    @8
    @5
    vy
    con0
    cA
    @4
    con0
    wcel
    #
    @8
    wa
    #
    @7
    @4
    cA
    wcel
    #
    @5
    wa
    @12
    @7
    wa
    #
    @13
    @5
    @14
    @4
    cA
    csdm
    wbr
    #
    @13
    @8
    @3
    @15
    @11
    @0
    @4
    @2
    cA
    ensdomtr
    ad2ant2l
    @11
    @0
    @15
    @13
    wi
    @8
    @3
    @4
    cA
    sdomel
    ad2ant2r
    mpd
    @8
    @5
    @11
    @7
    @8
    @1
    @2
    csdm
    wbr
    @2
    @4
    cen
    wbr
    @5
    @1
    vx
    vex
    canth2
    @4
    @2
    ensym
    @1
    @2
    @4
    sdomentr
    sylancr
    ad2antlr
    jca
    expcom
    reximdv2
    mpd
    ex
    ralimdv
end
