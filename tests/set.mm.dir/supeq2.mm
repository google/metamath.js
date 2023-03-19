include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crab.mm"
include "cuni.mm"
include "csup.mm"
include "rabeq.mm"
include "raleq.mm"
include "anbi2d.mm"
include "rabbidv.mm"
include "eqtrd.mm"
include "unieqd.mm"
include "df-sup.mm"
include "3eqtr4g.mm"

theorem supeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( B = C -> sup ( A , B , R ) = sup ( A , C , R ) )

  proof
    cB
    cC
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cA
    wral
    #
    @2
    @1
    cR
    wbr
    @2
    vz
    cv
    cR
    wbr
    vz
    cA
    wrex
    wi
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    crab
    #
    cuni
    @3
    @4
    vy
    cC
    wral
    #
    wa
    #
    vx
    cC
    crab
    #
    cuni
    cA
    cB
    cR
    csup
    cA
    cC
    cR
    csup
    @0
    @7
    @10
    @0
    @7
    @6
    vx
    cC
    crab
    @10
    @6
    vx
    cB
    cC
    rabeq
    @0
    @6
    @9
    vx
    cC
    @0
    @5
    @8
    @3
    @4
    vy
    cB
    cC
    raleq
    anbi2d
    rabbidv
    eqtrd
    unieqd
    vx
    vy
    vz
    cA
    cB
    cR
    df-sup
    vx
    vy
    vz
    cA
    cC
    cR
    df-sup
    3eqtr4g
end
