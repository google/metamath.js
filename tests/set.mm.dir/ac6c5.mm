include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "ac6c4.mm"
include "exsimpr.mm"
include "syl.mm"

theorem ac6c5
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  assume ac6c4.1: |- A e. _V
  assume ac6c4.2: |- B e. _V

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint B f
  disjoint A y
  disjoint A z
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
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
    ac6c4.1
    ac6c4.2
    ac6c4
    @1
    @2
    vf
    exsimpr
    syl
end
