include "cima.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "vex.mm"
include "breldm.mm"
include "pm4.71ri.mm"
include "rexbii.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"
include "bitr4i.mm"
include "elima.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem imaindm
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R " A ) = ( R " ( A i^i dom R ) )

  proof
    vx
    cR
    cA
    cima
    #
    cR
    cA
    cR
    cdm
    #
    cin
    #
    cima
    #
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
    wrex
    #
    @6
    vy
    @2
    wrex
    #
    @5
    @0
    wcel
    @5
    @3
    wcel
    @7
    @4
    @1
    wcel
    #
    @6
    wa
    #
    vy
    cA
    wrex
    @8
    @6
    @10
    vy
    cA
    @6
    @9
    @4
    @5
    cR
    vy
    vex
    vx
    vex
    #
    breldm
    pm4.71ri
    rexbii
    @6
    @10
    vy
    @2
    cA
    @4
    @2
    wcel
    #
    @6
    wa
    @4
    cA
    wcel
    #
    @9
    wa
    #
    @6
    wa
    @13
    @10
    wa
    @12
    @14
    @6
    @4
    cA
    @1
    elin
    anbi1i
    @13
    @9
    @6
    anass
    bitri
    rexbii2
    bitr4i
    vy
    @5
    cR
    cA
    @11
    elima
    vy
    @5
    cR
    @2
    @11
    elima
    3bitr4i
    eqriv
end
