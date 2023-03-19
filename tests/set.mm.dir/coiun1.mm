include "ciun.mm"
include "ccom.mm"
include "relco.mm"
include "wrel.mm"
include "reliun.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "mprgbir.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cop.mm"
include "eliun.mm"
include "df-br.mm"
include "rexbii.mm"
include "3bitr4i.mm"
include "anbi2i.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "rexcom4.mm"
include "vex.mm"
include "opelco.mm"
include "bitri.mm"
include "eqrelriiv.mm"

theorem coiun1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint B x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C y
  disjoint C z
  assert |- ( U_ x e. C A o. B ) = U_ x e. C ( A o. B )

  proof
    vy
    vz
    vx
    cC
    cA
    ciun
    #
    cB
    ccom
    #
    vx
    cC
    cA
    cB
    ccom
    #
    ciun
    #
    @0
    cB
    relco
    @3
    wrel
    @2
    wrel
    #
    vx
    cC
    vx
    cC
    @2
    reliun
    @4
    vx
    cv
    cC
    wcel
    cA
    cB
    relco
    a1i
    mprgbir
    vy
    cv
    #
    vw
    cv
    #
    cB
    wbr
    #
    @6
    vz
    cv
    #
    @0
    wbr
    #
    wa
    #
    vw
    wex
    #
    @7
    @6
    @8
    cA
    wbr
    #
    wa
    #
    vw
    wex
    #
    vx
    cC
    wrex
    #
    @5
    @8
    cop
    #
    @1
    wcel
    @16
    @3
    wcel
    #
    @11
    @13
    vx
    cC
    wrex
    #
    vw
    wex
    @15
    @10
    @18
    vw
    @10
    @7
    @12
    vx
    cC
    wrex
    #
    wa
    @18
    @9
    @19
    @7
    @6
    @8
    cop
    #
    @0
    wcel
    @20
    cA
    wcel
    #
    vx
    cC
    wrex
    @9
    @19
    vx
    @20
    cC
    cA
    eliun
    @6
    @8
    @0
    df-br
    @12
    @21
    vx
    cC
    @6
    @8
    cA
    df-br
    rexbii
    3bitr4i
    anbi2i
    @7
    @12
    vx
    cC
    r19.42v
    bitr4i
    exbii
    @13
    vx
    vw
    cC
    rexcom4
    bitr4i
    vw
    @5
    @8
    @0
    cB
    vy
    vex
    #
    vz
    vex
    #
    opelco
    @17
    @16
    @2
    wcel
    #
    vx
    cC
    wrex
    @15
    vx
    @16
    cC
    @2
    eliun
    @24
    @14
    vx
    cC
    vw
    @5
    @8
    cA
    cB
    @22
    @23
    opelco
    rexbii
    bitri
    3bitr4i
    eqrelriiv
end
