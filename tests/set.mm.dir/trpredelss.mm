include "wcel.mm"
include "wse.mm"
include "wa.mm"
include "ctrpred.mm"
include "wss.mm"
include "cv.mm"
include "cpred.mm"
include "wral.mm"
include "cvv.mm"
include "setlikespec.mm"
include "trpredss.mm"
include "syl.mm"
include "sselda.mm"
include "simplr.mm"
include "trpredtr.mm"
include "ralrimiv.mm"
include "adantr.mm"
include "imp.mm"
include "trpredmintr.mm"
include "syl22anc.mm"
include "ex.mm"

theorem trpredelss
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let vy: setvar y


  assert |- ( ( X e. A /\ R Se A ) -> ( Y e. TrPred ( R , A , X ) -> TrPred ( R , A , Y ) C_ TrPred ( R , A , X ) ) )

  proof
    cX
    cA
    wcel
    #
    cA
    cR
    wse
    #
    wa
    #
    cY
    cA
    cR
    cX
    ctrpred
    #
    wcel
    #
    cA
    cR
    cY
    ctrpred
    @3
    wss
    #
    @2
    @4
    wa
    cY
    cA
    wcel
    @1
    cA
    cR
    vy
    cv
    #
    cpred
    @3
    wss
    #
    vy
    @3
    wral
    #
    cA
    cR
    cY
    cpred
    @3
    wss
    #
    @5
    @2
    @3
    cA
    cY
    @2
    cA
    cR
    cX
    cpred
    cvv
    wcel
    @3
    cA
    wss
    cA
    cR
    cX
    setlikespec
    cA
    cvv
    cR
    cX
    trpredss
    syl
    sselda
    @0
    @1
    @4
    simplr
    @2
    @8
    @4
    @2
    @7
    vy
    @3
    cA
    cR
    cX
    @6
    trpredtr
    ralrimiv
    adantr
    @2
    @4
    @9
    cA
    cR
    cX
    cY
    trpredtr
    imp
    vy
    cA
    @3
    cR
    cY
    trpredmintr
    syl22anc
    ex
end
