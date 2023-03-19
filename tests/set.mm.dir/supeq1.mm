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
include "raleq.mm"
include "rexeq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rabbidv.mm"
include "unieqd.mm"
include "df-sup.mm"
include "3eqtr4g.mm"

theorem supeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( B = C -> sup ( B , A , R ) = sup ( C , A , R ) )

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
    #
    vy
    cB
    wral
    #
    @2
    @1
    cR
    wbr
    #
    @2
    vz
    cv
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    crab
    #
    cuni
    @3
    vy
    cC
    wral
    #
    @5
    @6
    vz
    cC
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    crab
    #
    cuni
    cB
    cA
    cR
    csup
    cC
    cA
    cR
    csup
    @0
    @11
    @17
    @0
    @10
    @16
    vx
    cA
    @0
    @4
    @12
    @9
    @15
    @3
    vy
    cB
    cC
    raleq
    @0
    @8
    @14
    vy
    cA
    @0
    @7
    @13
    @5
    @6
    vz
    cB
    cC
    rexeq
    imbi2d
    ralbidv
    anbi12d
    rabbidv
    unieqd
    vx
    vy
    vz
    cB
    cA
    cR
    df-sup
    vx
    vy
    vz
    cC
    cA
    cR
    df-sup
    3eqtr4g
end
