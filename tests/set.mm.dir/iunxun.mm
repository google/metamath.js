include "cun.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wo.mm"
include "rexun.mm"
include "eliun.mm"
include "orbi12i.mm"
include "bitr4i.mm"
include "elun.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iunxun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- U_ x e. ( A u. B ) C = ( U_ x e. A C u. U_ x e. B C )

  proof
    vy
    vx
    cA
    cB
    cun
    #
    cC
    ciun
    #
    vx
    cA
    cC
    ciun
    #
    vx
    cB
    cC
    ciun
    #
    cun
    #
    vy
    cv
    #
    cC
    wcel
    #
    vx
    @0
    wrex
    #
    @5
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wo
    #
    @5
    @1
    wcel
    @5
    @4
    wcel
    @7
    @6
    vx
    cA
    wrex
    #
    @6
    vx
    cB
    wrex
    #
    wo
    @10
    @6
    vx
    cA
    cB
    rexun
    @8
    @11
    @9
    @12
    vx
    @5
    cA
    cC
    eliun
    vx
    @5
    cB
    cC
    eliun
    orbi12i
    bitr4i
    vx
    @5
    @0
    cC
    eliun
    @5
    @2
    @3
    elun
    3bitr4i
    eqriv
end
