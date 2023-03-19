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

theorem cnvco1
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- `' ( `' A o. B ) = ( `' B o. A )

  proof
    vx
    vy
    cA
    ccnv
    #
    cB
    ccom
    #
    ccnv
    #
    cB
    ccnv
    #
    cA
    ccom
    #
    @1
    relcnv
    @3
    cA
    relco
    vy
    cv
    #
    vz
    cv
    #
    cB
    wbr
    #
    @6
    vx
    cv
    #
    @0
    wbr
    #
    wa
    #
    vz
    wex
    #
    @8
    @6
    cA
    wbr
    #
    @6
    @5
    @3
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
    @13
    @7
    @6
    @5
    cB
    vz
    vex
    #
    vy
    vex
    #
    brcnv
    bicomi
    @6
    @8
    cA
    @17
    vx
    vex
    #
    brcnv
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
    @18
    opelcnv
    vz
    @5
    @8
    @0
    cB
    @18
    @19
    opelco
    bitri
    vz
    @8
    @5
    @3
    cA
    @19
    @18
    opelco
    3bitr4i
    eqrelriiv
end
