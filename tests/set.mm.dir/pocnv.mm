include "wpo.mm"
include "ccnv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "poirr.mm"
include "vex.mm"
include "brcnv.mm"
include "sylnibr.mm"
include "w3a.mm"
include "wi.mm"
include "3anrev.mm"
include "potr.mm"
include "sylan2b.mm"
include "anbi12ci.mm"
include "3imtr4g.mm"
include "ispod.mm"

theorem pocnv
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Po A -> `' R Po A )

  proof
    cA
    cR
    wpo
    #
    vx
    vy
    vz
    cA
    cR
    ccnv
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    wa
    @2
    @2
    cR
    wbr
    @2
    @2
    @1
    wbr
    cA
    @2
    cR
    poirr
    @2
    @2
    cR
    vx
    vex
    #
    @4
    brcnv
    sylnibr
    @0
    @3
    vy
    cv
    #
    cA
    wcel
    #
    vz
    cv
    #
    cA
    wcel
    #
    w3a
    #
    wa
    @7
    @5
    cR
    wbr
    #
    @5
    @2
    cR
    wbr
    #
    wa
    #
    @7
    @2
    cR
    wbr
    #
    @2
    @5
    @1
    wbr
    #
    @5
    @7
    @1
    wbr
    #
    wa
    @2
    @7
    @1
    wbr
    @9
    @0
    @8
    @6
    @3
    w3a
    @12
    @13
    wi
    @3
    @6
    @8
    3anrev
    cA
    @7
    @5
    @2
    cR
    potr
    sylan2b
    @14
    @11
    @15
    @10
    @2
    @5
    cR
    @4
    vy
    vex
    #
    brcnv
    @5
    @7
    cR
    @16
    vz
    vex
    #
    brcnv
    anbi12ci
    @2
    @7
    cR
    @4
    @17
    brcnv
    3imtr4g
    ispod
end
