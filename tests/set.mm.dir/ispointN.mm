include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "pointsetN.mm"
include "eleq2d.mm"
include "cvv.mm"
include "snex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem ispointN
  let cA: class A
  let cD: class D
  let cP: class P
  let cK: class K
  let cX: class X
  let va: setvar a
  let vx: setvar x
  assume ispoint.a: |- A = ( Atoms ` K )
  assume ispoint.p: |- P = ( Points ` K )

  disjoint A a
  disjoint X a
  disjoint a x
  disjoint A x
  disjoint K x
  disjoint X x
  assert |- ( K e. D -> ( X e. P <-> E. a e. A X = { a } ) )

  proof
    cK
    cD
    wcel
    #
    cX
    cP
    wcel
    cX
    vx
    cv
    #
    va
    cv
    #
    csn
    #
    wceq
    #
    va
    cA
    wrex
    #
    vx
    cab
    #
    wcel
    cX
    @3
    wceq
    #
    va
    cA
    wrex
    #
    @0
    cP
    @6
    cX
    cA
    cD
    cP
    cK
    vx
    va
    ispoint.a
    ispoint.p
    pointsetN
    eleq2d
    @5
    @8
    vx
    cX
    @7
    cX
    cvv
    wcel
    #
    va
    cA
    @7
    @9
    @3
    cvv
    wcel
    @2
    snex
    cX
    @3
    cvv
    eleq1
    mpbiri
    rexlimivw
    @1
    cX
    wceq
    @4
    @7
    va
    cA
    @1
    cX
    @3
    eqeq1
    rexbidv
    elab3
    syl6bb
end
