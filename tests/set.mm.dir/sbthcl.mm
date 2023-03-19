include "cen.mm"
include "cdom.mm"
include "ccnv.mm"
include "cin.mm"
include "relen.mm"
include "wss.mm"
include "wrel.mm"
include "inss1.mm"
include "reldom.mm"
include "relss.mm"
include "mp2.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "brin.mm"
include "vex.mm"
include "brcnv.mm"
include "anbi2i.mm"
include "sbthb.mm"
include "3bitrri.mm"
include "eqbrriv.mm"

theorem sbthcl
  let vx: setvar x
  let vy: setvar y


  assert |- ~~ = ( ~<_ i^i `' ~<_ )

  proof
    vx
    vy
    cen
    cdom
    cdom
    ccnv
    #
    cin
    #
    relen
    @1
    cdom
    wss
    cdom
    wrel
    @1
    wrel
    cdom
    @0
    inss1
    reldom
    @1
    cdom
    relss
    mp2
    vx
    cv
    #
    vy
    cv
    #
    @1
    wbr
    @2
    @3
    cdom
    wbr
    #
    @2
    @3
    @0
    wbr
    #
    wa
    @4
    @3
    @2
    cdom
    wbr
    #
    wa
    @2
    @3
    cen
    wbr
    @2
    @3
    cdom
    @0
    brin
    @5
    @6
    @4
    @2
    @3
    cdom
    vx
    vex
    vy
    vex
    brcnv
    anbi2i
    @2
    @3
    sbthb
    3bitrri
    eqbrriv
end
