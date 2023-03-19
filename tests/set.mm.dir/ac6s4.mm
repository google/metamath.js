include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wfn.mm"
include "cfv.mm"
include "wa.mm"
include "n0.mm"
include "ralbii.mm"
include "eleq1.mm"
include "ac6s2.mm"
include "sylbi.mm"

theorem ac6s4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vy: setvar y
  assume ac6s4.1: |- A e. _V

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint B f
  disjoint f y
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A. x e. A B =/= (/) -> E. f ( f Fn A /\ A. x e. A ( f ` x ) e. B ) )

  proof
    cB
    c0
    wne
    #
    vx
    cA
    wral
    vy
    cv
    #
    cB
    wcel
    #
    vy
    wex
    #
    vx
    cA
    wral
    vf
    cv
    #
    cA
    wfn
    vx
    cv
    @4
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    wa
    vf
    wex
    @0
    @3
    vx
    cA
    vy
    cB
    n0
    ralbii
    @2
    @6
    vx
    vy
    cA
    vf
    ac6s4.1
    @1
    @5
    cB
    eleq1
    ac6s2
    sylbi
end
