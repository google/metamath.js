include "ciun.mm"
include "crn.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "wrex.mm"
include "rexcom4.mm"
include "vex.mm"
include "elrn2.mm"
include "rexbii.mm"
include "eliun.mm"
include "exbii.mm"
include "3bitr4ri.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem rniun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z


  assert |- ran U_ x e. A B = U_ x e. A ran B

  proof
    vz
    vx
    cA
    cB
    ciun
    #
    crn
    #
    vx
    cA
    cB
    crn
    #
    ciun
    #
    vy
    cv
    vz
    cv
    #
    cop
    #
    @0
    wcel
    #
    vy
    wex
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
    cB
    wcel
    #
    vy
    wex
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
    wex
    @9
    @7
    @10
    vx
    vy
    cA
    rexcom4
    @8
    @11
    vx
    cA
    vy
    @4
    cB
    vz
    vex
    #
    elrn2
    rexbii
    @6
    @12
    vy
    vx
    @5
    cA
    cB
    eliun
    exbii
    3bitr4ri
    vy
    @4
    @0
    @13
    elrn2
    vx
    @4
    cA
    @2
    eliun
    3bitr4i
    eqriv
end
