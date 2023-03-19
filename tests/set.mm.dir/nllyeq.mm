include "wceq.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "ctop.mm"
include "crab.mm"
include "cnlly.mm"
include "eleq2.mm"
include "rexbidv.mm"
include "2ralbidv.mm"
include "rabbidv.mm"
include "df-nlly.mm"
include "3eqtr4g.mm"

theorem nllyeq
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


  assert |- ( A = B -> N-Locally A = N-Locally B )

  proof
    cA
    cB
    wceq
    #
    vj
    cv
    #
    vu
    cv
    crest
    co
    #
    cA
    wcel
    #
    vu
    vy
    cv
    csn
    @1
    cnei
    cfv
    cfv
    vx
    cv
    #
    cpw
    cin
    #
    wrex
    #
    vy
    @4
    wral
    vx
    @1
    wral
    #
    vj
    ctop
    crab
    @2
    cB
    wcel
    #
    vu
    @5
    wrex
    #
    vy
    @4
    wral
    vx
    @1
    wral
    #
    vj
    ctop
    crab
    cA
    cnlly
    cB
    cnlly
    @0
    @7
    @10
    vj
    ctop
    @0
    @6
    @9
    vx
    vy
    @1
    @4
    @0
    @3
    @8
    vu
    @5
    cA
    cB
    @2
    eleq2
    rexbidv
    2ralbidv
    rabbidv
    vx
    vy
    vu
    cA
    vj
    df-nlly
    vx
    vy
    vu
    cB
    vj
    df-nlly
    3eqtr4g
end
