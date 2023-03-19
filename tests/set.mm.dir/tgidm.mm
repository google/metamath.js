include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eltg3.mm"
include "ax-mp.mm"
include "cpw.mm"
include "cin.mm"
include "ciun.mm"
include "uniiun.mm"
include "simpr.mm"
include "sselda.mm"
include "eltg4i.mm"
include "syl.mm"
include "iuneq2dv.mm"
include "syl5eq.mm"
include "iuncom4.mm"
include "syl6eq.mm"
include "wral.mm"
include "inss1.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "a1i.mm"
include "eltg3i.mm"
include "sylan2.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "bastg.mm"
include "tgss.mm"
include "sylancr.mm"
include "eqssd.mm"

theorem tgidm
  let cB: class B
  let cV: class V
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( B e. V -> ( topGen ` ( topGen ` B ) ) = ( topGen ` B ) )

  proof
    cB
    cV
    wcel
    #
    cB
    ctg
    cfv
    #
    ctg
    cfv
    #
    @1
    @0
    vx
    @2
    @1
    vx
    cv
    #
    @2
    wcel
    #
    vy
    cv
    #
    @1
    wss
    #
    @3
    @5
    cuni
    #
    wceq
    #
    wa
    #
    vy
    wex
    #
    @0
    @3
    @1
    wcel
    #
    @1
    cvv
    wcel
    #
    @4
    @10
    wb
    cB
    ctg
    fvex
    #
    vy
    @3
    @1
    cvv
    eltg3
    ax-mp
    @0
    @9
    @11
    vy
    @0
    @6
    @8
    @11
    @0
    @6
    wa
    #
    @11
    @8
    @7
    @1
    wcel
    @14
    @7
    vz
    @5
    cB
    vz
    cv
    #
    cpw
    #
    cin
    #
    ciun
    #
    cuni
    #
    @1
    @14
    @7
    vz
    @5
    @17
    cuni
    #
    ciun
    #
    @19
    @14
    @7
    vz
    @5
    @15
    ciun
    @21
    vz
    @5
    uniiun
    @14
    vz
    @5
    @15
    @20
    @14
    @15
    @5
    wcel
    wa
    @15
    @1
    wcel
    @15
    @20
    wceq
    @14
    @5
    @1
    @15
    @0
    @6
    simpr
    sselda
    @15
    cB
    eltg4i
    syl
    iuneq2dv
    syl5eq
    vz
    @5
    @17
    iuncom4
    syl6eq
    @6
    @0
    @18
    cB
    wss
    #
    @19
    @1
    wcel
    @22
    @6
    @22
    @17
    cB
    wss
    #
    vz
    @5
    wral
    @23
    vz
    @5
    cB
    @16
    inss1
    rgenw
    vz
    @5
    @17
    cB
    iunss
    mpbir
    a1i
    @18
    cB
    cV
    eltg3i
    sylan2
    eqeltrd
    @3
    @7
    @1
    eleq1
    syl5ibrcom
    expimpd
    exlimdv
    syl5bi
    ssrdv
    @0
    @12
    cB
    @1
    wss
    @1
    @2
    wss
    @13
    cB
    cV
    bastg
    cB
    @1
    cvv
    tgss
    sylancr
    eqssd
end
