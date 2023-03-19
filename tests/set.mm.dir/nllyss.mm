include "wss.mm"
include "cnlly.mm"
include "cv.mm"
include "ctop.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "ssel.mm"
include "reximdv.mm"
include "ralimdv.mm"
include "anim2d.mm"
include "isnlly.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem nllyss
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


  assert |- ( A C_ B -> N-Locally A C_ N-Locally B )

  proof
    cA
    cB
    wss
    #
    vj
    cA
    cnlly
    #
    cB
    cnlly
    #
    @0
    vj
    cv
    #
    ctop
    wcel
    #
    @3
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
    @3
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
    @7
    wral
    #
    vx
    @3
    wral
    #
    wa
    @4
    @5
    cB
    wcel
    #
    vu
    @8
    wrex
    #
    vy
    @7
    wral
    #
    vx
    @3
    wral
    #
    wa
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @11
    @15
    @4
    @0
    @10
    @14
    vx
    @3
    @0
    @9
    @13
    vy
    @7
    @0
    @6
    @12
    vu
    @8
    cA
    cB
    @5
    ssel
    reximdv
    ralimdv
    ralimdv
    anim2d
    vx
    vy
    vu
    cA
    @3
    isnlly
    vx
    vy
    vu
    cB
    @3
    isnlly
    3imtr4g
    ssrdv
end
