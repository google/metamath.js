include "ciun.mm"
include "cxp.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "rexcom.mm"
include "wa.mm"
include "wex.mm"
include "eliun.mm"
include "anbi1i.mm"
include "exbii.mm"
include "df-rex.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "r19.41v.mm"
include "3bitri.mm"
include "3bitr4i.mm"
include "elxp2.mm"
include "eqriv.mm"

theorem xpiundi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint C x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  assert |- ( C X. U_ x e. A B ) = U_ x e. A ( C X. B )

  proof
    vz
    cC
    vx
    cA
    cB
    ciun
    #
    cxp
    #
    vx
    cA
    cC
    cB
    cxp
    #
    ciun
    #
    vz
    cv
    #
    vw
    cv
    vy
    cv
    #
    cop
    wceq
    #
    vy
    @0
    wrex
    #
    vw
    cC
    wrex
    #
    @4
    @2
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @6
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    vw
    cC
    wrex
    @11
    vw
    cC
    wrex
    #
    vx
    cA
    wrex
    @8
    @10
    @11
    vw
    vx
    cC
    cA
    rexcom
    @7
    @12
    vw
    cC
    @5
    @0
    wcel
    #
    @6
    wa
    #
    vy
    wex
    @5
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @6
    wa
    #
    vy
    wex
    #
    @7
    @12
    @15
    @18
    vy
    @14
    @17
    @6
    vx
    @5
    cA
    cB
    eliun
    anbi1i
    exbii
    @6
    vy
    @0
    df-rex
    @12
    @16
    @6
    wa
    #
    vy
    wex
    #
    vx
    cA
    wrex
    @20
    vx
    cA
    wrex
    #
    vy
    wex
    @19
    @11
    @21
    vx
    cA
    @6
    vy
    cB
    df-rex
    rexbii
    @20
    vx
    vy
    cA
    rexcom4
    @22
    @18
    vy
    @16
    @6
    vx
    cA
    r19.41v
    exbii
    3bitri
    3bitr4i
    rexbii
    @9
    @13
    vx
    cA
    vw
    vy
    @4
    cC
    cB
    elxp2
    rexbii
    3bitr4i
    vw
    vy
    @4
    cC
    @0
    elxp2
    vx
    @4
    cA
    @2
    eliun
    3bitr4i
    eqriv
end
