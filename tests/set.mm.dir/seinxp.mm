include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cin.mm"
include "wse.mm"
include "wb.mm"
include "brinxp.mm"
include "ancoms.mm"
include "rabbidva.mm"
include "eleq1d.mm"
include "ralbiia.mm"
include "df-se.mm"
include "3bitr4i.mm"

theorem seinxp
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Se A <-> ( R i^i ( A X. A ) ) Se A )

  proof
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    vy
    cA
    crab
    #
    cvv
    wcel
    #
    vx
    cA
    wral
    @0
    @1
    cR
    cA
    cA
    cxp
    cin
    #
    wbr
    #
    vy
    cA
    crab
    #
    cvv
    wcel
    #
    vx
    cA
    wral
    cA
    cR
    wse
    cA
    @5
    wse
    @4
    @8
    vx
    cA
    @1
    cA
    wcel
    #
    @3
    @7
    cvv
    @9
    @2
    @6
    vy
    cA
    @0
    cA
    wcel
    @9
    @2
    @6
    wb
    @0
    @1
    cA
    cA
    cR
    brinxp
    ancoms
    rabbidva
    eleq1d
    ralbiia
    vx
    vy
    cA
    cR
    df-se
    vx
    vy
    cA
    @5
    df-se
    3bitr4i
end
