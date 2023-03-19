include "wfn.mm"
include "crn.mm"
include "cint.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "ciin.mm"
include "fnrnfv.mm"
include "inteqd.mm"
include "fvex.mm"
include "dfiin2.mm"
include "syl6reqr.mm"

theorem fniinfv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  assert |- ( F Fn A -> |^|_ x e. A ( F ` x ) = |^| ran F )

  proof
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cint
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
    cint
    vx
    cA
    @3
    ciin
    @0
    @1
    @4
    vx
    vy
    cA
    cF
    fnrnfv
    inteqd
    vx
    vy
    cA
    @3
    @2
    cF
    fvex
    dfiin2
    syl6reqr
end
