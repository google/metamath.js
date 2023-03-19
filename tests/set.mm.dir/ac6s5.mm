include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "ac6s4.mm"
include "exsimpr.mm"
include "syl.mm"

theorem ac6s5
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
  assert |- ( A. x e. A B =/= (/) -> E. f A. x e. A ( f ` x ) e. B )

  proof
    cB
    c0
    wne
    vx
    cA
    wral
    vf
    cv
    #
    cA
    wfn
    #
    vx
    cv
    @0
    cfv
    cB
    wcel
    vx
    cA
    wral
    #
    wa
    vf
    wex
    @2
    vf
    wex
    vx
    cA
    cB
    vf
    ac6s4.1
    ac6s4
    @1
    @2
    vf
    exsimpr
    syl
end
