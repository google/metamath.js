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
include "disj.mm"
include "rexbii.mm"
include "3imtr4i.mm"

theorem zfregOLD
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume zfregOLD.1: |- A e. _V

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A =/= (/) -> E. x e. A ( x i^i A ) = (/) )

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
    @0
    cA
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
    zfregOLD.1
    zfregclOLD
    vx
    cA
    n0
    @2
    @1
    vx
    cA
    vy
    @0
    cA
    disj
    rexbii
    3imtr4i
end
