include "cdm.mm"
include "cin.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "19.8a.mm"
include "ancoms.mm"
include "vex.mm"
include "elima2.mm"
include "sylibr.mm"
include "simpl.mm"
include "brcnv.mm"
include "jca.mm"
include "eximi.mm"
include "eldm.mm"
include "anbi1i.mm"
include "elin.mm"
include "19.41v.mm"
include "3bitr4i.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem dminss
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( dom R i^i A ) C_ ( `' R " ( R " A ) )

  proof
    vx
    cR
    cdm
    #
    cA
    cin
    #
    cR
    ccnv
    #
    cR
    cA
    cima
    #
    cima
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @5
    cA
    wcel
    #
    wa
    #
    vy
    wex
    #
    @6
    @3
    wcel
    #
    @6
    @5
    @2
    wbr
    #
    wa
    #
    vy
    wex
    @5
    @1
    wcel
    #
    @5
    @4
    wcel
    @9
    @13
    vy
    @9
    @11
    @12
    @9
    @8
    @7
    wa
    #
    vx
    wex
    #
    @11
    @8
    @7
    @16
    @15
    vx
    19.8a
    ancoms
    vx
    @6
    cR
    cA
    vy
    vex
    #
    elima2
    sylibr
    @9
    @7
    @12
    @7
    @8
    simpl
    @6
    @5
    cR
    @17
    vx
    vex
    #
    brcnv
    sylibr
    jca
    eximi
    @5
    @0
    wcel
    #
    @8
    wa
    @7
    vy
    wex
    #
    @8
    wa
    @14
    @10
    @19
    @20
    @8
    vy
    @5
    cR
    @18
    eldm
    anbi1i
    @5
    @0
    cA
    elin
    @7
    @8
    vy
    19.41v
    3bitr4i
    vy
    @5
    @2
    @3
    @18
    elima2
    3imtr4i
    ssriv
end
