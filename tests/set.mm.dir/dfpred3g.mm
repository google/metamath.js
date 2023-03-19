include "cv.mm"
include "cpred.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "predeq3.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eqeq12d.mm"
include "vex.mm"
include "dfpred3.mm"
include "vtoclg.mm"

theorem dfpred3g
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cV: class V
  let cX: class X
  let vx: setvar x

  disjoint R y
  disjoint A y
  disjoint X y
  disjoint R x
  disjoint x y
  disjoint A x
  disjoint X x
  assert |- ( X e. V -> Pred ( R , A , X ) = { y e. A | y R X } )

  proof
    cA
    cR
    vx
    cv
    #
    cpred
    #
    vy
    cv
    #
    @0
    cR
    wbr
    #
    vy
    cA
    crab
    #
    wceq
    cA
    cR
    cX
    cpred
    #
    @2
    cX
    cR
    wbr
    #
    vy
    cA
    crab
    #
    wceq
    vx
    cX
    cV
    @0
    cX
    wceq
    #
    @1
    @5
    @4
    @7
    cA
    cR
    @0
    cX
    predeq3
    @8
    @3
    @6
    vy
    cA
    @0
    cX
    @2
    cR
    breq2
    rabbidv
    eqeq12d
    vy
    cA
    cR
    @0
    vx
    vex
    dfpred3
    vtoclg
end
