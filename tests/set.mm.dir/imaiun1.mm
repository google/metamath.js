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
include "anbi2i.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "3bitr4ri.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem imaiun1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  assert |- ( U_ x e. A B " C ) = U_ x e. A ( B " C )

  proof
    vy
    vx
    cA
    cB
    ciun
    #
    cC
    cima
    #
    vx
    cA
    cB
    cC
    cima
    #
    ciun
    #
    vz
    cv
    #
    cC
    wcel
    #
    @4
    vy
    cv
    #
    cop
    #
    @0
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
    cA
    wrex
    #
    @6
    @1
    wcel
    @6
    @3
    wcel
    @5
    @7
    cB
    wcel
    #
    wa
    #
    vz
    wex
    #
    vx
    cA
    wrex
    @14
    vx
    cA
    wrex
    #
    vz
    wex
    @12
    @10
    @14
    vx
    vz
    cA
    rexcom4
    @11
    @15
    vx
    cA
    vz
    @6
    cB
    cC
    vy
    vex
    #
    elima3
    rexbii
    @9
    @16
    vz
    @9
    @5
    @13
    vx
    cA
    wrex
    #
    wa
    @16
    @8
    @18
    @5
    vx
    @7
    cA
    cB
    eliun
    anbi2i
    @5
    @13
    vx
    cA
    r19.42v
    bitr4i
    exbii
    3bitr4ri
    vz
    @6
    @0
    cC
    @17
    elima3
    vx
    @6
    cA
    @2
    eliun
    3bitr4i
    eqriv
end
