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
include "breq.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "rabbidv.mm"
include "unieqd.mm"
include "df-sup.mm"
include "3eqtr4g.mm"

theorem supeq3
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R = S -> sup ( A , B , R ) = sup ( A , B , S ) )

  proof
    cR
    cS
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
    #
    wn
    #
    vy
    cA
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
    #
    cR
    wbr
    #
    vz
    cA
    wrex
    #
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
    @1
    @2
    cS
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @2
    @1
    cS
    wbr
    #
    @2
    @7
    cS
    wbr
    #
    vz
    cA
    wrex
    #
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
    cA
    cB
    cR
    csup
    cA
    cB
    cS
    csup
    @0
    @13
    @23
    @0
    @12
    @22
    vx
    cB
    @0
    @5
    @16
    @11
    @21
    @0
    @4
    @15
    vy
    cA
    @0
    @3
    @14
    @1
    @2
    cR
    cS
    breq
    notbid
    ralbidv
    @0
    @10
    @20
    vy
    cB
    @0
    @6
    @17
    @9
    @19
    @2
    @1
    cR
    cS
    breq
    @0
    @8
    @18
    vz
    cA
    @2
    @7
    cR
    cS
    breq
    rexbidv
    imbi12d
    ralbidv
    anbi12d
    rabbidv
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
    cB
    cS
    df-sup
    3eqtr4g
end
