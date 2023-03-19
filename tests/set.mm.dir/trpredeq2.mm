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
include "predeq2.mm"
include "iuneq2d.mm"
include "mpteq2dv.mm"
include "wa.mm"
include "rdgeq12.mm"
include "reseq1d.mm"
include "syl2anc.mm"
include "rneqd.mm"
include "unieqd.mm"
include "df-trpred.mm"
include "3eqtr4g.mm"

theorem trpredeq2
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let va: setvar a
  let vy: setvar y
  let cS: class S
  let cY: class Y


  assert |- ( A = B -> TrPred ( R , A , X ) = TrPred ( R , B , X ) )

  proof
    cA
    cB
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
    cB
    cR
    @2
    cpred
    #
    ciun
    #
    cmpt
    #
    cB
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
    cA
    cR
    cX
    ctrpred
    cB
    cR
    cX
    ctrpred
    @0
    @9
    @16
    @0
    @8
    @15
    @0
    @5
    @12
    wceq
    #
    @6
    @13
    wceq
    #
    @8
    @15
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
    cB
    cR
    @2
    predeq2
    iuneq2d
    mpteq2dv
    cA
    cB
    cR
    cX
    predeq2
    @17
    @18
    wa
    @7
    @14
    com
    @6
    @13
    @5
    @12
    rdgeq12
    reseq1d
    syl2anc
    rneqd
    unieqd
    vy
    cA
    cR
    cX
    va
    df-trpred
    vy
    cB
    cR
    cX
    va
    df-trpred
    3eqtr4g
end
