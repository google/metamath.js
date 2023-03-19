include "ciun.mm"
include "cxp.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "rexcom4.mm"
include "df-rex.mm"
include "rexbii.mm"
include "eliun.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "3bitr4ri.mm"
include "elxp2.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem xpiundir
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
  assert |- ( U_ x e. A B X. C ) = U_ x e. A ( B X. C )

  proof
    vz
    vx
    cA
    cB
    ciun
    #
    cC
    cxp
    #
    vx
    cA
    cB
    cC
    cxp
    #
    ciun
    #
    vz
    cv
    #
    vy
    cv
    #
    vw
    cv
    cop
    wceq
    vw
    cC
    wrex
    #
    vy
    @0
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
    @5
    @0
    wcel
    #
    @6
    wa
    #
    vy
    wex
    #
    @6
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    @7
    @9
    @5
    cB
    wcel
    #
    @6
    wa
    #
    vy
    wex
    #
    vx
    cA
    wrex
    @16
    vx
    cA
    wrex
    #
    vy
    wex
    @14
    @12
    @16
    vx
    vy
    cA
    rexcom4
    @13
    @17
    vx
    cA
    @6
    vy
    cB
    df-rex
    rexbii
    @11
    @18
    vy
    @11
    @15
    vx
    cA
    wrex
    #
    @6
    wa
    @18
    @10
    @19
    @6
    vx
    @5
    cA
    cB
    eliun
    anbi1i
    @15
    @6
    vx
    cA
    r19.41v
    bitr4i
    exbii
    3bitr4ri
    @6
    vy
    @0
    df-rex
    @8
    @13
    vx
    cA
    vy
    vw
    @4
    cB
    cC
    elxp2
    rexbii
    3bitr4i
    vy
    vw
    @4
    @0
    cC
    elxp2
    vx
    @4
    cA
    @2
    eliun
    3bitr4i
    eqriv
end
