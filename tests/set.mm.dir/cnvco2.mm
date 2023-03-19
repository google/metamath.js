include "ccnv.mm"
include "ccom.mm"
include "relcnv.mm"
include "relco.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "cop.mm"
include "wcel.mm"
include "vex.mm"
include "brcnv.mm"
include "bicomi.mm"
include "anbi12ci.mm"
include "exbii.mm"
include "opelcnv.mm"
include "opelco.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem cnvco2
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- `' ( A o. `' B ) = ( B o. `' A )

  proof
    vx
    vy
    cA
    cB
    ccnv
    #
    ccom
    #
    ccnv
    #
    cB
    cA
    ccnv
    #
    ccom
    #
    @1
    relcnv
    cB
    @3
    relco
    vy
    cv
    #
    vz
    cv
    #
    @0
    wbr
    #
    @6
    vx
    cv
    #
    cA
    wbr
    #
    wa
    #
    vz
    wex
    #
    @8
    @6
    @3
    wbr
    #
    @6
    @5
    cB
    wbr
    #
    wa
    #
    vz
    wex
    @8
    @5
    cop
    #
    @2
    wcel
    #
    @15
    @4
    wcel
    @10
    @14
    vz
    @7
    @13
    @9
    @12
    @5
    @6
    cB
    vy
    vex
    #
    vz
    vex
    #
    brcnv
    @12
    @9
    @8
    @6
    cA
    vx
    vex
    #
    @18
    brcnv
    bicomi
    anbi12ci
    exbii
    @16
    @5
    @8
    cop
    @1
    wcel
    @11
    @8
    @5
    @1
    @19
    @17
    opelcnv
    vz
    @5
    @8
    cA
    @0
    @17
    @19
    opelco
    bitri
    vz
    @8
    @5
    cB
    @3
    @19
    @17
    opelco
    3bitr4i
    eqrelriiv
end
