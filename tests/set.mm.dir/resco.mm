include "ccom.mm"
include "cres.mm"
include "relres.mm"
include "relco.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "vex.mm"
include "brco.mm"
include "anbi1i.mm"
include "19.41v.mm"
include "an32.mm"
include "brres.mm"
include "bitr4i.mm"
include "exbii.mm"
include "3bitr2i.mm"
include "3bitr4i.mm"
include "eqbrriv.mm"

theorem resco
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A o. B ) |` C ) = ( A o. ( B |` C ) )

  proof
    vx
    vy
    cA
    cB
    ccom
    #
    cC
    cres
    #
    cA
    cB
    cC
    cres
    #
    ccom
    #
    @0
    cC
    relres
    cA
    @2
    relco
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    @4
    cC
    wcel
    #
    wa
    #
    @4
    vz
    cv
    #
    @2
    wbr
    #
    @9
    @5
    cA
    wbr
    #
    wa
    #
    vz
    wex
    #
    @4
    @5
    @1
    wbr
    @4
    @5
    @3
    wbr
    @8
    @4
    @9
    cB
    wbr
    #
    @11
    wa
    #
    vz
    wex
    #
    @7
    wa
    @15
    @7
    wa
    #
    vz
    wex
    @13
    @6
    @16
    @7
    vz
    @4
    @5
    cA
    cB
    vx
    vex
    #
    vy
    vex
    #
    brco
    anbi1i
    @15
    @7
    vz
    19.41v
    @17
    @12
    vz
    @17
    @14
    @7
    wa
    #
    @11
    wa
    @12
    @14
    @11
    @7
    an32
    @10
    @20
    @11
    @4
    @9
    cB
    cC
    vz
    vex
    brres
    anbi1i
    bitr4i
    exbii
    3bitr2i
    @4
    @5
    @0
    cC
    @19
    brres
    vz
    @4
    @5
    cA
    @2
    @18
    @19
    brco
    3bitr4i
    eqbrriv
end
