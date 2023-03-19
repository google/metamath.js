include "ciin.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "r19.12.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "rexbii.mm"
include "eliun.mm"
include "ralbii.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem iuniin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint x y
  disjoint A y
  disjoint B x
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint B z
  disjoint C z
  assert |- U_ x e. A |^|_ y e. B C C_ |^|_ y e. B U_ x e. A C

  proof
    vz
    vx
    cA
    vy
    cB
    cC
    ciin
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
    ciin
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
    wral
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    #
    @4
    cC
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cA
    wrex
    @10
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    @6
    @8
    @10
    vx
    vy
    cA
    cB
    r19.12
    @5
    @11
    vx
    cA
    @4
    cvv
    wcel
    #
    @5
    @11
    wb
    vz
    vex
    #
    vy
    @4
    cB
    cC
    cvv
    eliin
    ax-mp
    rexbii
    @7
    @12
    vy
    cB
    vx
    @4
    cA
    cC
    eliun
    ralbii
    3imtr4i
    vx
    @4
    cA
    @0
    eliun
    @13
    @9
    @8
    wb
    @14
    vy
    @4
    cB
    @2
    cvv
    eliin
    ax-mp
    3imtr4i
    ssriv
end
