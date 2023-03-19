include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "ctop.mm"
include "crab.mm"
include "clly.mm"
include "eleq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "2ralbidv.mm"
include "rabbidv.mm"
include "df-lly.mm"
include "3eqtr4g.mm"

theorem llyeq
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cJ: class J
  let cV: class V


  assert |- ( A = B -> Locally A = Locally B )

  proof
    cA
    cB
    wceq
    #
    vy
    cv
    vu
    cv
    #
    wcel
    #
    vj
    cv
    #
    @1
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vu
    @3
    vx
    cv
    #
    cpw
    cin
    #
    wrex
    #
    vy
    @7
    wral
    vx
    @3
    wral
    #
    vj
    ctop
    crab
    @2
    @4
    cB
    wcel
    #
    wa
    #
    vu
    @8
    wrex
    #
    vy
    @7
    wral
    vx
    @3
    wral
    #
    vj
    ctop
    crab
    cA
    clly
    cB
    clly
    @0
    @10
    @14
    vj
    ctop
    @0
    @9
    @13
    vx
    vy
    @3
    @7
    @0
    @6
    @12
    vu
    @8
    @0
    @5
    @11
    @2
    cA
    cB
    @4
    eleq2
    anbi2d
    rexbidv
    2ralbidv
    rabbidv
    vx
    vy
    vu
    cA
    vj
    df-lly
    vx
    vy
    vu
    cB
    vj
    df-lly
    3eqtr4g
end
