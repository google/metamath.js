include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wceq.mm"
include "raleq.mm"
include "exbidv.mm"
include "ac4.mm"
include "vtocl.mm"

theorem ac4c
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  assume ac4c.1: |- A e. _V

  disjoint f x
  disjoint A x
  disjoint A f
  disjoint x y
  disjoint f y
  disjoint A y
  assert |- E. f A. x e. A ( x =/= (/) -> ( f ` x ) e. x )

  proof
    vx
    cv
    #
    c0
    wne
    @0
    vf
    cv
    cfv
    @0
    wcel
    wi
    #
    vx
    vy
    cv
    #
    wral
    #
    vf
    wex
    @1
    vx
    cA
    wral
    #
    vf
    wex
    vy
    cA
    ac4c.1
    @2
    cA
    wceq
    @3
    @4
    vf
    @1
    vx
    @2
    cA
    raleq
    exbidv
    vy
    vx
    vf
    ac4
    vtocl
end
