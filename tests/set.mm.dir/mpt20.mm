include "c0.mm"
include "cmpt2.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cop.mm"
include "wex.mm"
include "cab.mm"
include "df-mpt2.mm"
include "df-oprab.mm"
include "noel.mm"
include "simprll.mm"
include "mto.mm"
include "nex.mm"
include "abf.mm"
include "3eqtri.mm"

theorem mpt20
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vz: setvar z


  assert |- ( x e. (/) , y e. B |-> C ) = (/)

  proof
    vx
    vy
    c0
    cB
    cC
    cmpt2
    vx
    cv
    #
    c0
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    vz
    cv
    #
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    vw
    cv
    @0
    @2
    cop
    @4
    cop
    wceq
    #
    @6
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    vx
    wex
    #
    vw
    cab
    c0
    vx
    vy
    vz
    c0
    cB
    cC
    df-mpt2
    @6
    vx
    vy
    vz
    vw
    df-oprab
    @11
    vw
    @10
    vx
    @9
    vy
    @8
    vz
    @8
    @1
    @0
    noel
    @7
    @1
    @3
    @5
    simprll
    mto
    nex
    nex
    nex
    abf
    3eqtri
end
