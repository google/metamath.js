include "cima.mm"
include "cin.mm"
include "ccnv.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "vex.mm"
include "brcnv.mm"
include "19.8a.mm"
include "sylan2br.mm"
include "ancoms.mm"
include "anim2i.mm"
include "simprl.mm"
include "jca.mm"
include "anassrs.mm"
include "elin.mm"
include "elima2.mm"
include "anbi2i.mm"
include "bitri.mm"
include "anbi1i.mm"
include "sylibr.mm"
include "eximi.mm"
include "19.41v.mm"
include "3bitr4i.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem imainss
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R " A ) i^i B ) C_ ( R " ( A i^i ( `' R " B ) ) )

  proof
    vy
    cR
    cA
    cima
    #
    cB
    cin
    #
    cR
    cA
    cR
    ccnv
    #
    cB
    cima
    #
    cin
    #
    cima
    #
    vx
    cv
    #
    cA
    wcel
    #
    @6
    vy
    cv
    #
    cR
    wbr
    #
    wa
    #
    @8
    cB
    wcel
    #
    wa
    #
    vx
    wex
    #
    @6
    @4
    wcel
    #
    @9
    wa
    #
    vx
    wex
    @8
    @1
    wcel
    #
    @8
    @5
    wcel
    @12
    @15
    vx
    @12
    @7
    @11
    @8
    @6
    @2
    wbr
    #
    wa
    #
    vy
    wex
    #
    wa
    #
    @9
    wa
    #
    @15
    @7
    @9
    @11
    @21
    @7
    @9
    @11
    wa
    #
    wa
    @20
    @9
    @22
    @19
    @7
    @11
    @9
    @19
    @9
    @11
    @17
    @19
    @8
    @6
    cR
    vy
    vex
    #
    vx
    vex
    #
    brcnv
    @18
    vy
    19.8a
    sylan2br
    ancoms
    anim2i
    @7
    @9
    @11
    simprl
    jca
    anassrs
    @14
    @20
    @9
    @14
    @7
    @6
    @3
    wcel
    #
    wa
    @20
    @6
    cA
    @3
    elin
    @25
    @19
    @7
    vy
    @6
    @2
    cB
    @24
    elima2
    anbi2i
    bitri
    anbi1i
    sylibr
    eximi
    @8
    @0
    wcel
    #
    @11
    wa
    @10
    vx
    wex
    #
    @11
    wa
    @16
    @13
    @26
    @27
    @11
    vx
    @8
    cR
    cA
    @23
    elima2
    anbi1i
    @8
    @0
    cB
    elin
    @10
    @11
    vx
    19.41v
    3bitr4i
    vx
    @8
    cR
    @4
    @23
    elima2
    3imtr4i
    ssriv
end
