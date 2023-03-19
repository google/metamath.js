include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "eliun.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "rexcom4.mm"
include "df-rex.mm"
include "bitri.mm"
include "rexbii.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iunxiun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint C y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  assert |- U_ x e. U_ y e. A B C = U_ y e. A U_ x e. B C

  proof
    vz
    vx
    vy
    cA
    cB
    ciun
    #
    cC
    ciun
    #
    vy
    cA
    vx
    cB
    cC
    ciun
    #
    ciun
    #
    vz
    cv
    #
    cC
    wcel
    #
    vx
    @0
    wrex
    #
    @4
    @2
    wcel
    #
    vy
    cA
    wrex
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    vx
    cv
    #
    @0
    wcel
    #
    @5
    wa
    #
    vx
    wex
    #
    @9
    cB
    wcel
    #
    @5
    wa
    #
    vx
    wex
    #
    vy
    cA
    wrex
    #
    @6
    @8
    @12
    @14
    vy
    cA
    wrex
    #
    vx
    wex
    @16
    @11
    @17
    vx
    @11
    @13
    vy
    cA
    wrex
    #
    @5
    wa
    @17
    @10
    @18
    @5
    vy
    @9
    cA
    cB
    eliun
    anbi1i
    @13
    @5
    vy
    cA
    r19.41v
    bitr4i
    exbii
    @14
    vy
    vx
    cA
    rexcom4
    bitr4i
    @5
    vx
    @0
    df-rex
    @7
    @15
    vy
    cA
    @7
    @5
    vx
    cB
    wrex
    @15
    vx
    @4
    cB
    cC
    eliun
    @5
    vx
    cB
    df-rex
    bitri
    rexbii
    3bitr4i
    vx
    @4
    @0
    cC
    eliun
    vy
    @4
    cA
    @2
    eliun
    3bitr4i
    eqriv
end
