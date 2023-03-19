include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "cin.mm"
include "wceq.mm"
include "zfregclOLD.mm"
include "n0.mm"
include "disjr.mm"
include "rexbii.mm"
include "3imtr4i.mm"

theorem zfreg2OLD
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume zfreg2OLD.1: |- A e. _V

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A =/= (/) -> E. x e. A ( A i^i x ) = (/) )

  proof
    vx
    cv
    #
    cA
    wcel
    vx
    wex
    vy
    cv
    cA
    wcel
    wn
    vy
    @0
    wral
    #
    vx
    cA
    wrex
    cA
    c0
    wne
    cA
    @0
    cin
    c0
    wceq
    #
    vx
    cA
    wrex
    vx
    vy
    cA
    zfreg2OLD.1
    zfregclOLD
    vx
    cA
    n0
    @2
    @1
    vx
    cA
    vy
    cA
    @0
    disjr
    rexbii
    3imtr4i
end
