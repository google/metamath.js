include "wfn.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "fnrnfv.mm"
include "eleq2d.mm"
include "cvv.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbii.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "elab3.mm"

theorem fvelrnb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let cY: class Y

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint Y x
  assert |- ( F Fn A -> ( B e. ran F <-> E. x e. A ( F ` x ) = B ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cF
    crn
    #
    wcel
    cB
    vy
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    wcel
    @4
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @0
    @1
    @7
    cB
    vx
    vy
    cA
    cF
    fnrnfv
    eleq2d
    @6
    @9
    vy
    cB
    @8
    cB
    cvv
    wcel
    #
    vx
    cA
    @8
    @4
    cvv
    wcel
    @10
    @3
    cF
    fvex
    @4
    cB
    cvv
    eleq1
    mpbii
    rexlimivw
    @2
    cB
    wceq
    #
    @5
    @8
    vx
    cA
    @11
    @5
    cB
    @4
    wceq
    @8
    @2
    cB
    @4
    eqeq1
    cB
    @4
    eqcom
    syl6bb
    rexbidv
    elab3
    syl6bb
end
