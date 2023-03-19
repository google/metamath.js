include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "rexcom.mm"
include "eliun.mm"
include "rexbii.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iuncom
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint B z
  disjoint C z
  assert |- U_ x e. A U_ y e. B C = U_ y e. B U_ x e. A C

  proof
    vz
    vx
    cA
    vy
    cB
    cC
    ciun
    #
    ciun
    #
    vy
    cB
    vx
    cA
    cC
    ciun
    #
    ciun
    #
    vz
    cv
    #
    @0
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    @2
    wcel
    #
    vy
    cB
    wrex
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @4
    cC
    wcel
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    @9
    vx
    cA
    wrex
    #
    vy
    cB
    wrex
    @6
    @8
    @9
    vx
    vy
    cA
    cB
    rexcom
    @5
    @10
    vx
    cA
    vy
    @4
    cB
    cC
    eliun
    rexbii
    @7
    @11
    vy
    cB
    vx
    @4
    cA
    cC
    eliun
    rexbii
    3bitr4i
    vx
    @4
    cA
    @0
    eliun
    vy
    @4
    cB
    @2
    eliun
    3bitr4i
    eqriv
end
