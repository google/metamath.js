include "cpred.mm"
include "wcel.mm"
include "ctrpred.mm"
include "com.mm"
include "cv.mm"
include "cvv.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "dftrpred2.mm"
include "wss.mm"
include "wral.mm"
include "trpredlem1.mm"
include "ralrimivw.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"

theorem trpredss
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let va: setvar a
  let vi: setvar i
  let vy: setvar y


  assert |- ( Pred ( R , A , X ) e. B -> TrPred ( R , A , X ) C_ A )

  proof
    cA
    cR
    cX
    cpred
    #
    cB
    wcel
    #
    cA
    cR
    cX
    ctrpred
    vi
    com
    vi
    cv
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
    @0
    crdg
    com
    cres
    cfv
    #
    ciun
    #
    cA
    vy
    cA
    cR
    vi
    cX
    va
    dftrpred2
    @1
    @2
    cA
    wss
    #
    vi
    com
    wral
    @3
    cA
    wss
    @1
    @4
    vi
    com
    vy
    cA
    cB
    cR
    vi
    cX
    va
    trpredlem1
    ralrimivw
    vi
    com
    @2
    cA
    iunss
    sylibr
    syl5eqss
end
