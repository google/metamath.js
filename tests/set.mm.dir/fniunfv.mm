include "wfn.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "fnrnfv.mm"
include "unieqd.mm"
include "fvex.mm"
include "dfiun2.mm"
include "syl6reqr.mm"

theorem fniunfv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint F y
  assert |- ( F Fn A -> U_ x e. A ( F ` x ) = U. ran F )

  proof
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cuni
    vy
    cv
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cuni
    vx
    cA
    @3
    ciun
    @0
    @1
    @4
    vx
    vy
    cA
    cF
    fnrnfv
    unieqd
    vx
    vy
    cA
    @3
    @2
    cF
    fvex
    dfiun2
    syl6reqr
end
