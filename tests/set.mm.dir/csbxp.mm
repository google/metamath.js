include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "csb.mm"
include "cxp.mm"
include "wsbc.mm"
include "csbab.mm"
include "sbcex2.mm"
include "sbcan.mm"
include "cvv.mm"
include "wb.mm"
include "sbcg.mm"
include "sbcel2.mm"
include "anbi12i.mm"
include "bitri.mm"
include "a1i.mm"
include "anbi12d.mm"
include "wn.mm"
include "sbcex.mm"
include "con3i.mm"
include "intnand.mm"
include "c0.mm"
include "noel.mm"
include "csbprc.mm"
include "neleqtrrd.mm"
include "2falsed.mm"
include "pm2.61i.mm"
include "exbii.mm"
include "abbii.mm"
include "eqtri.mm"
include "copab.mm"
include "df-xp.mm"
include "df-opab.mm"
include "csbeq2i.mm"
include "3eqtr4i.mm"

theorem csbxp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- [_ A / x ]_ ( B X. C ) = ( [_ A / x ]_ B X. [_ A / x ]_ C )

  proof
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
    @0
    cB
    wcel
    #
    @1
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
    @2
    @0
    vx
    cA
    cB
    csb
    #
    wcel
    #
    @1
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
    @11
    @13
    cxp
    #
    @10
    @8
    vx
    cA
    wsbc
    #
    vz
    cab
    @19
    @8
    vx
    vz
    cA
    csbab
    @22
    @18
    vz
    @22
    @7
    vx
    cA
    wsbc
    #
    vw
    wex
    @18
    @7
    vw
    vx
    cA
    sbcex2
    @23
    @17
    vw
    @23
    @6
    vx
    cA
    wsbc
    #
    vy
    wex
    @17
    @6
    vy
    vx
    cA
    sbcex2
    @24
    @16
    vy
    @24
    @2
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
    #
    @16
    @2
    @5
    vx
    cA
    sbcan
    cA
    cvv
    wcel
    #
    @27
    @16
    wb
    @28
    @25
    @2
    @26
    @15
    @2
    vx
    cA
    cvv
    sbcg
    @26
    @15
    wb
    @28
    @26
    @3
    vx
    cA
    wsbc
    #
    @4
    vx
    cA
    wsbc
    #
    wa
    @15
    @3
    @4
    vx
    cA
    sbcan
    @29
    @12
    @30
    @14
    vx
    cA
    @0
    cB
    sbcel2
    vx
    cA
    @1
    cC
    sbcel2
    anbi12i
    bitri
    a1i
    anbi12d
    @28
    wn
    #
    @27
    @16
    @31
    @26
    @25
    @26
    @28
    @5
    vx
    cA
    sbcex
    con3i
    intnand
    @31
    @15
    @2
    @31
    @14
    @12
    @31
    @13
    c0
    @1
    @1
    c0
    wcel
    wn
    @31
    @1
    noel
    a1i
    vx
    cA
    cC
    csbprc
    neleqtrrd
    intnand
    intnand
    2falsed
    pm2.61i
    bitri
    exbii
    bitri
    exbii
    bitri
    abbii
    eqtri
    vx
    cA
    @20
    @9
    @20
    @5
    vw
    vy
    copab
    @9
    vw
    vy
    cB
    cC
    df-xp
    @5
    vw
    vy
    vz
    df-opab
    eqtri
    csbeq2i
    @21
    @15
    vw
    vy
    copab
    @19
    vw
    vy
    @11
    @13
    df-xp
    @15
    vw
    vy
    vz
    df-opab
    eqtri
    3eqtr4i
end
