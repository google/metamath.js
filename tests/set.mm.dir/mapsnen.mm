include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "ovex.mm"
include "wcel.mm"
include "fvexd.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "mapsn.mm"
include "abeq2i.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "df-rex.mm"
include "3bitr2i.mm"
include "fveq1.mm"
include "vex.mm"
include "fvsn.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "equcom.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "anbi2i.mm"
include "anass.mm"
include "ancom.mm"
include "exbii.mm"
include "eleq1.mm"
include "opeq2.mm"
include "sneqd.mm"
include "anbi12d.mm"
include "ceqsexv.mm"
include "3bitri.mm"
include "en2i.mm"

theorem mapsnen
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume mapsnen.1: |- A e. _V
  assume mapsnen.2: |- B e. _V


  assert |- ( A ^m { B } ) ~~ A

  proof
    vz
    vw
    cA
    cB
    csn
    #
    cmap
    co
    #
    cA
    cB
    vz
    cv
    #
    cfv
    #
    cB
    vw
    cv
    #
    cop
    #
    csn
    #
    cA
    @0
    cmap
    ovex
    mapsnen.1
    @2
    @1
    wcel
    #
    cB
    @2
    fvexd
    @6
    cvv
    wcel
    @4
    cA
    wcel
    #
    @5
    snex
    a1i
    @7
    @4
    @3
    wceq
    #
    wa
    #
    vy
    cv
    #
    cA
    wcel
    #
    @2
    cB
    @11
    cop
    #
    csn
    #
    wceq
    #
    @9
    wa
    #
    wa
    #
    vy
    wex
    #
    @11
    @4
    wceq
    #
    @12
    @15
    wa
    #
    wa
    #
    vy
    wex
    @8
    @2
    @6
    wceq
    #
    wa
    #
    @10
    @15
    vy
    cA
    wrex
    #
    @9
    wa
    @16
    vy
    cA
    wrex
    @18
    @7
    @24
    @9
    @24
    vz
    @1
    vy
    cA
    cB
    vz
    mapsnen.1
    mapsnen.2
    mapsn
    abeq2i
    anbi1i
    @15
    @9
    vy
    cA
    r19.41v
    @16
    vy
    cA
    df-rex
    3bitr2i
    @17
    @21
    vy
    @17
    @12
    @15
    @19
    wa
    #
    wa
    @20
    @19
    wa
    @21
    @16
    @25
    @12
    @15
    @9
    @19
    @15
    @9
    @4
    @11
    wceq
    @19
    @15
    @3
    @11
    @4
    @15
    @3
    cB
    @14
    cfv
    @11
    cB
    @2
    @14
    fveq1
    cB
    @11
    mapsnen.2
    vy
    vex
    fvsn
    syl6eq
    eqeq2d
    vw
    vy
    equcom
    syl6bb
    pm5.32i
    anbi2i
    @12
    @15
    @19
    anass
    @20
    @19
    ancom
    3bitr2i
    exbii
    @20
    @23
    vy
    @4
    vw
    vex
    @19
    @12
    @8
    @15
    @22
    @11
    @4
    cA
    eleq1
    @19
    @14
    @6
    @2
    @19
    @13
    @5
    @11
    @4
    cB
    opeq2
    sneqd
    eqeq2d
    anbi12d
    ceqsexv
    3bitri
    en2i
end
