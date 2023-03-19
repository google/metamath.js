include "wss.mm"
include "wral.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wi.mm"
include "ssel.mm"
include "ralimi.mm"
include "rexim.mm"
include "syl.mm"
include "eliun.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem ss2iun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( A. x e. A B C_ C -> U_ x e. A B C_ U_ x e. A C )

  proof
    cB
    cC
    wss
    #
    vx
    cA
    wral
    #
    vy
    vx
    cA
    cB
    ciun
    #
    vx
    cA
    cC
    ciun
    #
    @1
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    cC
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    @2
    wcel
    @4
    @3
    wcel
    @1
    @5
    @7
    wi
    #
    vx
    cA
    wral
    @6
    @8
    wi
    @0
    @9
    vx
    cA
    cB
    cC
    @4
    ssel
    ralimi
    @5
    @7
    vx
    cA
    rexim
    syl
    vx
    @4
    cA
    cB
    eliun
    vx
    @4
    cA
    cC
    eliun
    3imtr4g
    ssrdv
end
