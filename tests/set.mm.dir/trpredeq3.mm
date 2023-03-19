include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "cpred.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "cuni.mm"
include "ctrpred.mm"
include "predeq3.mm"
include "rdgeq2.mm"
include "syl.mm"
include "reseq1d.mm"
include "rneqd.mm"
include "unieqd.mm"
include "df-trpred.mm"
include "3eqtr4g.mm"

theorem trpredeq3
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vy: setvar y
  let cS: class S
  let cB: class B


  assert |- ( X = Y -> TrPred ( R , A , X ) = TrPred ( R , A , Y ) )

  proof
    cX
    cY
    wceq
    #
    va
    cvv
    vy
    va
    cv
    cA
    cR
    vy
    cv
    cpred
    ciun
    cmpt
    #
    cA
    cR
    cX
    cpred
    #
    crdg
    #
    com
    cres
    #
    crn
    #
    cuni
    @1
    cA
    cR
    cY
    cpred
    #
    crdg
    #
    com
    cres
    #
    crn
    #
    cuni
    cA
    cR
    cX
    ctrpred
    cA
    cR
    cY
    ctrpred
    @0
    @5
    @9
    @0
    @4
    @8
    @0
    @3
    @7
    com
    @0
    @2
    @6
    wceq
    @3
    @7
    wceq
    cA
    cR
    cX
    cY
    predeq3
    @2
    @6
    @1
    rdgeq2
    syl
    reseq1d
    rneqd
    unieqd
    vy
    cA
    cR
    cX
    va
    df-trpred
    vy
    cA
    cR
    cY
    va
    df-trpred
    3eqtr4g
end
