include "wss.mm"
include "clly.mm"
include "cv.mm"
include "ctop.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "ssel.mm"
include "anim2d.mm"
include "reximdv.mm"
include "ralimdv.mm"
include "islly.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem llyss
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


  assert |- ( A C_ B -> Locally A C_ Locally B )

  proof
    cA
    cB
    wss
    #
    vj
    cA
    clly
    #
    cB
    clly
    #
    @0
    vj
    cv
    #
    ctop
    wcel
    #
    vy
    cv
    vu
    cv
    #
    wcel
    #
    @3
    @5
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
    @10
    wral
    #
    vx
    @3
    wral
    #
    wa
    @4
    @6
    @7
    cB
    wcel
    #
    wa
    #
    vu
    @11
    wrex
    #
    vy
    @10
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
    @14
    @19
    @4
    @0
    @13
    @18
    vx
    @3
    @0
    @12
    @17
    vy
    @10
    @0
    @9
    @16
    vu
    @11
    @0
    @8
    @15
    @6
    cA
    cB
    @7
    ssel
    anim2d
    reximdv
    ralimdv
    ralimdv
    anim2d
    vx
    vy
    vu
    cA
    @3
    islly
    vx
    vy
    vu
    cB
    @3
    islly
    3imtr4g
    ssrdv
end
