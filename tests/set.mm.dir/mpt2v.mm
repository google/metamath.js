include "cvv.mm"
include "cmpt2.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "df-mpt2.mm"
include "vex.mm"
include "pm3.2i.mm"
include "biantrur.mm"
include "oprabbii.mm"
include "eqtr4i.mm"

theorem mpt2v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C

  disjoint x z
  disjoint y z
  disjoint C z
  assert |- ( x e. _V , y e. _V |-> C ) = { <. <. x , y >. , z >. | z = C }

  proof
    vx
    vy
    cvv
    cvv
    cC
    cmpt2
    vx
    cv
    cvv
    wcel
    #
    vy
    cv
    cvv
    wcel
    #
    wa
    #
    vz
    cv
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    @3
    vx
    vy
    vz
    coprab
    vx
    vy
    vz
    cvv
    cvv
    cC
    df-mpt2
    @3
    @4
    vx
    vy
    vz
    @2
    @3
    @0
    @1
    vx
    vex
    vy
    vex
    pm3.2i
    biantrur
    oprabbii
    eqtr4i
end
