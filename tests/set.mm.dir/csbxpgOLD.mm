include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "csb.mm"
include "cxp.mm"
include "wsbc.mm"
include "csbab.mm"
include "sbcex2.mm"
include "sbcan.mm"
include "sbcg.mm"
include "wb.mm"
include "sbcel2.mm"
include "a1i.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "exbidv.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "copab.mm"
include "df-xp.mm"
include "df-opab.mm"
include "eqtri.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbxpgOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. D -> [_ A / x ]_ ( B X. C ) = ( [_ A / x ]_ B X. [_ A / x ]_ C ) )

  proof
    cA
    cD
    wcel
    #
    vx
    cA
    vz
    cv
    vw
    cv
    #
    vy
    cv
    #
    cop
    wceq
    #
    @1
    cB
    wcel
    #
    @2
    cC
    wcel
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vw
    wex
    #
    vz
    cab
    #
    csb
    #
    @3
    @1
    vx
    cA
    cB
    csb
    #
    wcel
    #
    @2
    vx
    cA
    cC
    csb
    #
    wcel
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vw
    wex
    #
    vz
    cab
    #
    vx
    cA
    cB
    cC
    cxp
    #
    csb
    @12
    @14
    cxp
    #
    @0
    @11
    @9
    vx
    cA
    wsbc
    #
    vz
    cab
    @20
    @9
    vx
    vz
    cA
    csbab
    @0
    @23
    @19
    vz
    @23
    @8
    vx
    cA
    wsbc
    #
    vw
    wex
    @0
    @19
    @8
    vw
    vx
    cA
    sbcex2
    @0
    @24
    @18
    vw
    @24
    @7
    vx
    cA
    wsbc
    #
    vy
    wex
    @0
    @18
    @7
    vy
    vx
    cA
    sbcex2
    @0
    @25
    @17
    vy
    @25
    @3
    vx
    cA
    wsbc
    #
    @6
    vx
    cA
    wsbc
    #
    wa
    @0
    @17
    @3
    @6
    vx
    cA
    sbcan
    @0
    @26
    @3
    @27
    @16
    @3
    vx
    cA
    cD
    sbcg
    @27
    @4
    vx
    cA
    wsbc
    #
    @5
    vx
    cA
    wsbc
    #
    wa
    @0
    @16
    @4
    @5
    vx
    cA
    sbcan
    @0
    @28
    @13
    @29
    @15
    @28
    @13
    wb
    @0
    vx
    cA
    @1
    cB
    sbcel2
    a1i
    @29
    @15
    wb
    @0
    vx
    cA
    @2
    cC
    sbcel2
    a1i
    anbi12d
    syl5bb
    anbi12d
    syl5bb
    exbidv
    syl5bb
    exbidv
    syl5bb
    abbidv
    syl5eq
    vx
    cA
    @21
    @10
    @21
    @6
    vw
    vy
    copab
    @10
    vw
    vy
    cB
    cC
    df-xp
    @6
    vw
    vy
    vz
    df-opab
    eqtri
    csbeq2i
    @22
    @16
    vw
    vy
    copab
    @20
    vw
    vy
    @12
    @14
    df-xp
    @16
    vw
    vy
    vz
    df-opab
    eqtri
    3eqtr4g
end
