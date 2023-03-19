include "ciun.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "wrex.mm"
include "rexcom4.mm"
include "vex.mm"
include "eldm2.mm"
include "rexbii.mm"
include "eliun.mm"
include "exbii.mm"
include "3bitr4ri.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem dmiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z


  assert |- dom U_ x e. A B = U_ x e. A dom B

  proof
    vy
    vx
    cA
    cB
    ciun
    #
    cdm
    #
    vx
    cA
    cB
    cdm
    #
    ciun
    #
    vy
    cv
    #
    vz
    cv
    cop
    #
    @0
    wcel
    #
    vz
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
    vz
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
    vz
    wex
    @9
    @7
    @10
    vx
    vz
    cA
    rexcom4
    @8
    @11
    vx
    cA
    vz
    @4
    cB
    vy
    vex
    #
    eldm2
    rexbii
    @6
    @12
    vz
    vx
    @5
    cA
    cB
    eliun
    exbii
    3bitr4ri
    vz
    @4
    @0
    @13
    eldm2
    vx
    @4
    cA
    @2
    eliun
    3bitr4i
    eqriv
end
