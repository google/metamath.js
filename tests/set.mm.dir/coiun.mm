include "ciun.mm"
include "ccom.mm"
include "relco.mm"
include "wrel.mm"
include "reliun.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "mprgbir.mm"
include "cop.mm"
include "wrex.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "eliun.mm"
include "df-br.mm"
include "rexbii.mm"
include "3bitr4i.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "rexcom4.mm"
include "vex.mm"
include "opelco.mm"
include "eqrelriiv.mm"

theorem coiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C y
  disjoint C z
  assert |- ( A o. U_ x e. C B ) = U_ x e. C ( A o. B )

  proof
    vy
    vz
    cA
    vx
    cC
    cB
    ciun
    #
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
    cA
    @0
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
    vz
    cv
    #
    cop
    #
    @1
    wcel
    #
    @7
    @2
    wcel
    #
    vx
    cC
    wrex
    #
    @7
    @3
    wcel
    @5
    vw
    cv
    #
    @0
    wbr
    #
    @11
    @6
    cA
    wbr
    #
    wa
    #
    vw
    wex
    #
    @5
    @11
    cB
    wbr
    #
    @13
    wa
    #
    vw
    wex
    #
    vx
    cC
    wrex
    #
    @8
    @10
    @15
    @17
    vx
    cC
    wrex
    #
    vw
    wex
    @19
    @14
    @20
    vw
    @14
    @16
    vx
    cC
    wrex
    #
    @13
    wa
    @20
    @12
    @21
    @13
    @5
    @11
    cop
    #
    @0
    wcel
    @22
    cB
    wcel
    #
    vx
    cC
    wrex
    @12
    @21
    vx
    @22
    cC
    cB
    eliun
    @5
    @11
    @0
    df-br
    @16
    @23
    vx
    cC
    @5
    @11
    cB
    df-br
    rexbii
    3bitr4i
    anbi1i
    @16
    @13
    vx
    cC
    r19.41v
    bitr4i
    exbii
    @17
    vx
    vw
    cC
    rexcom4
    bitr4i
    vw
    @5
    @6
    cA
    @0
    vy
    vex
    #
    vz
    vex
    #
    opelco
    @9
    @18
    vx
    cC
    vw
    @5
    @6
    cA
    cB
    @24
    @25
    opelco
    rexbii
    3bitr4i
    vx
    @7
    cC
    @2
    eliun
    bitr4i
    eqrelriiv
end
