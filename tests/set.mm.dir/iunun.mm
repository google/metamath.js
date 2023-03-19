include "cun.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wo.mm"
include "r19.43.mm"
include "elun.mm"
include "rexbii.mm"
include "eliun.mm"
include "orbi12i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iunun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- U_ x e. A ( B u. C ) = ( U_ x e. A B u. U_ x e. A C )

  proof
    vy
    vx
    cA
    cB
    cC
    cun
    #
    ciun
    #
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
    cun
    #
    vy
    cv
    #
    @0
    wcel
    #
    vx
    cA
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
    @5
    cB
    wcel
    #
    @5
    cC
    wcel
    #
    wo
    #
    vx
    cA
    wrex
    @11
    vx
    cA
    wrex
    #
    @12
    vx
    cA
    wrex
    #
    wo
    @7
    @10
    @11
    @12
    vx
    cA
    r19.43
    @6
    @13
    vx
    cA
    @5
    cB
    cC
    elun
    rexbii
    @8
    @14
    @9
    @15
    vx
    @5
    cA
    cB
    eliun
    vx
    @5
    cA
    cC
    eliun
    orbi12i
    3bitr4i
    vx
    @5
    cA
    @0
    eliun
    @5
    @2
    @3
    elun
    3bitr4i
    eqriv
end
