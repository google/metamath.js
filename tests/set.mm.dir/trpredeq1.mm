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
include "predeq1.mm"
include "iuneq2d.mm"
include "mpteq2dv.mm"
include "rdgeq12.mm"
include "syl2anc.mm"
include "reseq1d.mm"
include "rneqd.mm"
include "unieqd.mm"
include "df-trpred.mm"
include "3eqtr4g.mm"

theorem trpredeq1
  let cA: class A
  let cR: class R
  let cS: class S
  let cX: class X
  let va: setvar a
  let vy: setvar y
  let cB: class B
  let cY: class Y


  assert |- ( R = S -> TrPred ( R , A , X ) = TrPred ( S , A , X ) )

  proof
    cR
    cS
    wceq
    #
    va
    cvv
    vy
    va
    cv
    #
    cA
    cR
    vy
    cv
    #
    cpred
    #
    ciun
    #
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
    va
    cvv
    vy
    @1
    cA
    cS
    @2
    cpred
    #
    ciun
    #
    cmpt
    #
    cA
    cS
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
    cA
    cR
    cX
    ctrpred
    cA
    cS
    cX
    ctrpred
    @0
    @9
    @16
    @0
    @8
    @15
    @0
    @7
    @14
    com
    @0
    @5
    @12
    wceq
    @6
    @13
    wceq
    @7
    @14
    wceq
    @0
    va
    cvv
    @4
    @11
    @0
    vy
    @1
    @3
    @10
    cA
    cR
    cS
    @2
    predeq1
    iuneq2d
    mpteq2dv
    cA
    cR
    cS
    cX
    predeq1
    @6
    @13
    @5
    @12
    rdgeq12
    syl2anc
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
    cS
    cX
    va
    df-trpred
    3eqtr4g
end
