include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "coprab.mm"
include "cunc.mm"
include "fveq1.mm"
include "breqd.mm"
include "oprabbidv.mm"
include "df-unc.mm"
include "3eqtr4g.mm"

theorem unceq
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A = B -> uncurry A = uncurry B )

  proof
    cA
    cB
    wceq
    #
    vy
    cv
    #
    vz
    cv
    #
    vx
    cv
    #
    cA
    cfv
    #
    wbr
    #
    vx
    vy
    vz
    coprab
    @1
    @2
    @3
    cB
    cfv
    #
    wbr
    #
    vx
    vy
    vz
    coprab
    cA
    cunc
    cB
    cunc
    @0
    @5
    @7
    vx
    vy
    vz
    @0
    @4
    @6
    @1
    @2
    @3
    cA
    cB
    fveq1
    breqd
    oprabbidv
    vx
    vy
    vz
    cA
    df-unc
    vx
    vy
    vz
    cB
    df-unc
    3eqtr4g
end
