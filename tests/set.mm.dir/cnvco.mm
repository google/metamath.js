include "cv.mm"
include "ccom.mm"
include "wbr.mm"
include "copab.mm"
include "ccnv.mm"
include "wa.mm"
include "wex.mm"
include "exancom.mm"
include "vex.mm"
include "brco.mm"
include "brcnv.mm"
include "anbi12i.mm"
include "exbii.mm"
include "3bitr4i.mm"
include "opabbii.mm"
include "df-cnv.mm"
include "df-co.mm"
include "3eqtr4i.mm"

theorem cnvco
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- `' ( A o. B ) = ( `' B o. `' A )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cA
    cB
    ccom
    #
    wbr
    #
    vy
    vx
    copab
    @1
    vz
    cv
    #
    cA
    ccnv
    #
    wbr
    #
    @4
    @0
    cB
    ccnv
    #
    wbr
    #
    wa
    #
    vz
    wex
    #
    vy
    vx
    copab
    @2
    ccnv
    @7
    @5
    ccom
    @3
    @10
    vy
    vx
    @0
    @4
    cB
    wbr
    #
    @4
    @1
    cA
    wbr
    #
    wa
    vz
    wex
    @12
    @11
    wa
    #
    vz
    wex
    @3
    @10
    @11
    @12
    vz
    exancom
    vz
    @0
    @1
    cA
    cB
    vx
    vex
    #
    vy
    vex
    #
    brco
    @9
    @13
    vz
    @6
    @12
    @8
    @11
    @1
    @4
    cA
    @15
    vz
    vex
    #
    brcnv
    @4
    @0
    cB
    @16
    @14
    brcnv
    anbi12i
    exbii
    3bitr4i
    opabbii
    vy
    vx
    @2
    df-cnv
    vy
    vx
    vz
    @7
    @5
    df-co
    3eqtr4i
end
