include "ciun.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "rexcom4.mm"
include "vex.mm"
include "elima3.mm"
include "rexbii.mm"
include "eliun.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "3bitr4ri.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem imaiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  assert |- ( A " U_ x e. B C ) = U_ x e. B ( A " C )

  proof
    vy
    cA
    vx
    cB
    cC
    ciun
    #
    cima
    #
    vx
    cB
    cA
    cC
    cima
    #
    ciun
    #
    vz
    cv
    #
    @0
    wcel
    #
    @4
    vy
    cv
    #
    cop
    cA
    wcel
    #
    wa
    #
    vz
    wex
    #
    @6
    @2
    wcel
    #
    vx
    cB
    wrex
    #
    @6
    @1
    wcel
    @6
    @3
    wcel
    @4
    cC
    wcel
    #
    @7
    wa
    #
    vz
    wex
    #
    vx
    cB
    wrex
    @13
    vx
    cB
    wrex
    #
    vz
    wex
    @11
    @9
    @13
    vx
    vz
    cB
    rexcom4
    @10
    @14
    vx
    cB
    vz
    @6
    cA
    cC
    vy
    vex
    #
    elima3
    rexbii
    @8
    @15
    vz
    @8
    @12
    vx
    cB
    wrex
    #
    @7
    wa
    @15
    @5
    @17
    @7
    vx
    @4
    cB
    cC
    eliun
    anbi1i
    @12
    @7
    vx
    cB
    r19.41v
    bitr4i
    exbii
    3bitr4ri
    vz
    @6
    cA
    @0
    @16
    elima3
    vx
    @6
    cB
    @2
    eliun
    3bitr4i
    eqriv
end
