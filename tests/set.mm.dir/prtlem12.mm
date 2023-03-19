include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "wceq.mm"
include "wrel.mm"
include "relopab.mm"
include "releq.mm"
include "mpbiri.mm"

theorem prtlem12
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let c.sm: class .~

  disjoint x y
  assert |- ( .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) } -> Rel .~ )

  proof
    c.sm
    vx
    vu
    wel
    vy
    vu
    wel
    wa
    vu
    cA
    wrex
    #
    vx
    vy
    copab
    #
    wceq
    c.sm
    wrel
    @1
    wrel
    @0
    vx
    vy
    relopab
    c.sm
    @1
    releq
    mpbiri
end
