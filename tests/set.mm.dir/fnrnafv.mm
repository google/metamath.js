include "wfn.mm"
include "crn.mm"
include "cv.mm"
include "cafv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "dfafn5a.mm"
include "rneqd.mm"
include "eqid.mm"
include "rnmpt.mm"
include "syl6eq.mm"

theorem fnrnafv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cB: class B
  let vk: setvar k

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- ( F Fn A -> ran F = { y | E. x e. A y = ( F ''' x ) } )

  proof
    cF
    cA
    wfn
    #
    cF
    crn
    vx
    cA
    vx
    cv
    cF
    cafv
    #
    cmpt
    #
    crn
    vy
    cv
    @1
    wceq
    vx
    cA
    wrex
    vy
    cab
    @0
    cF
    @2
    vx
    cA
    cF
    dfafn5a
    rneqd
    vx
    vy
    cA
    @1
    @2
    @2
    eqid
    rnmpt
    syl6eq
end
