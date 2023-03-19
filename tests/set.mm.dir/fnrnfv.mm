include "wfn.mm"
include "crn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "dffn5.mm"
include "rneq.mm"
include "sylbi.mm"
include "eqid.mm"
include "rnmpt.mm"
include "syl6eq.mm"

theorem fnrnfv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cB: class B
  let cY: class Y

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint B x
  disjoint B y
  disjoint Y x
  assert |- ( F Fn A -> ran F = { y | E. x e. A y = ( F ` x ) } )

  proof
    cF
    cA
    wfn
    #
    cF
    crn
    #
    vx
    cA
    vx
    cv
    cF
    cfv
    #
    cmpt
    #
    crn
    #
    vy
    cv
    @2
    wceq
    vx
    cA
    wrex
    vy
    cab
    @0
    cF
    @3
    wceq
    @1
    @4
    wceq
    vx
    cA
    cF
    dffn5
    cF
    @3
    rneq
    sylbi
    vx
    vy
    cA
    @2
    @3
    @3
    eqid
    rnmpt
    syl6eq
end
