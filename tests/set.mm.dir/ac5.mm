include "cv.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "fneq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "dfac4.mm"
include "axaci.mm"
include "vtocl.mm"

theorem ac5
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  assume ac5.1: |- A e. _V

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint f y
  disjoint x y
  disjoint A y
  assert |- E. f ( f Fn A /\ A. x e. A ( x =/= (/) -> ( f ` x ) e. x ) )

  proof
    vf
    cv
    #
    vy
    cv
    #
    wfn
    #
    vx
    cv
    #
    c0
    wne
    @3
    @0
    cfv
    @3
    wcel
    wi
    #
    vx
    @1
    wral
    #
    wa
    #
    vf
    wex
    #
    @0
    cA
    wfn
    #
    @4
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    vy
    cA
    ac5.1
    @1
    cA
    wceq
    #
    @6
    @10
    vf
    @11
    @2
    @8
    @5
    @9
    @1
    cA
    @0
    fneq2
    @4
    vx
    @1
    cA
    raleq
    anbi12d
    exbidv
    @7
    vy
    vy
    vx
    vf
    dfac4
    axaci
    vtocl
end
