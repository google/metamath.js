include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "wvhc2.mm"
include "wtru.mm"
include "vex.mm"
include "vd01.mm"
include "idn1.mm"
include "elpwi.mm"
include "el1.mm"
include "sstr.mm"
include "ancoms.mm"
include "el12.mm"
include "elpwgdedVD.mm"
include "un0.1.mm"
include "int2.mm"
include "gen11.mm"
include "dfss2.mm"
include "biimpri.mm"
include "in1.mm"

theorem sspwimpVD
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ B -> ~P A C_ ~P B )

  proof
    cA
    cB
    wss
    #
    cA
    cpw
    #
    cB
    cpw
    #
    wss
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @4
    @2
    wcel
    #
    wi
    #
    vx
    wal
    #
    @3
    @0
    @7
    vx
    @0
    @5
    @6
    @4
    cvv
    wcel
    #
    @0
    @5
    wvhc2
    #
    @4
    cB
    wss
    #
    @6
    @9
    wtru
    vx
    vex
    vd01
    #
    @0
    @0
    @4
    cA
    wss
    #
    @11
    @5
    @0
    idn1
    @5
    @5
    @13
    @5
    idn1
    @4
    cA
    elpwi
    el1
    @13
    @0
    @11
    @4
    cA
    cB
    sstr
    ancoms
    el12
    #
    wtru
    @10
    @4
    cB
    @12
    @14
    elpwgdedVD
    un0.1
    int2
    gen11
    @3
    @8
    vx
    @1
    @2
    dfss2
    biimpri
    el1
    in1
end
