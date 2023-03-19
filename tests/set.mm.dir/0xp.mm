include "c0.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "noel.mm"
include "simprl.mm"
include "mto.mm"
include "nex.mm"
include "elxp.mm"
include "mtbir.mm"
include "nel0.mm"

theorem 0xp
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( (/) X. A ) = (/)

  proof
    vz
    c0
    cA
    cxp
    #
    vz
    cv
    #
    @0
    wcel
    @1
    vx
    cv
    #
    vy
    cv
    #
    cop
    wceq
    #
    @2
    c0
    wcel
    #
    @3
    cA
    wcel
    #
    wa
    wa
    #
    vy
    wex
    #
    vx
    wex
    @8
    vx
    @7
    vy
    @7
    @5
    @2
    noel
    @4
    @5
    @6
    simprl
    mto
    nex
    nex
    vx
    vy
    @1
    c0
    cA
    elxp
    mtbir
    nel0
end
