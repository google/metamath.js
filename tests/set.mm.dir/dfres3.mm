include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "crn.mm"
include "df-res.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "wb.mm"
include "eleq1.mm"
include "vex.mm"
include "biantru.mm"
include "opelrn.mm"
include "biantrud.mm"
include "syl5bbr.mm"
include "syl6bi.mm"
include "com12.mm"
include "pm5.32d.mm"
include "2exbidv.mm"
include "elxp.mm"
include "3bitr4g.mm"
include "pm5.32i.mm"
include "elin.mm"
include "bitr4i.mm"
include "ineqri.mm"
include "eqtri.mm"

theorem dfres3
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A |` B ) = ( A i^i ( B X. ran A ) )

  proof
    cA
    cB
    cres
    cA
    cB
    cvv
    cxp
    #
    cin
    cA
    cB
    cA
    crn
    #
    cxp
    #
    cin
    #
    cA
    cB
    df-res
    vx
    cA
    @0
    @3
    vx
    cv
    #
    cA
    wcel
    #
    @4
    @0
    wcel
    #
    wa
    @5
    @4
    @2
    wcel
    #
    wa
    @4
    @3
    wcel
    @5
    @6
    @7
    @5
    @4
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    @8
    cB
    wcel
    #
    @9
    cvv
    wcel
    #
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    @11
    @12
    @9
    @1
    wcel
    #
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    @6
    @7
    @5
    @15
    @18
    vy
    vz
    @5
    @11
    @14
    @17
    @11
    @5
    @14
    @17
    wb
    #
    @11
    @5
    @10
    cA
    wcel
    #
    @19
    @4
    @10
    cA
    eleq1
    @14
    @12
    @20
    @17
    @13
    @12
    vz
    vex
    #
    biantru
    @20
    @16
    @12
    @8
    @9
    cA
    vy
    vex
    @21
    opelrn
    biantrud
    syl5bbr
    syl6bi
    com12
    pm5.32d
    2exbidv
    vy
    vz
    @4
    cB
    cvv
    elxp
    vy
    vz
    @4
    cB
    @1
    elxp
    3bitr4g
    pm5.32i
    @4
    cA
    @2
    elin
    bitr4i
    ineqri
    eqtri
end
