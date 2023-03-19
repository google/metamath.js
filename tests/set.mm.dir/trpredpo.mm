include "wpo.mm"
include "wcel.mm"
include "wse.mm"
include "w3a.mm"
include "ctrpred.mm"
include "cpred.mm"
include "cv.mm"
include "wss.mm"
include "wral.mm"
include "simp2.mm"
include "simp3.mm"
include "wa.mm"
include "predpo.mm"
include "ralrimiv.mm"
include "3adant3.mm"
include "ssid.mm"
include "a1i.mm"
include "trpredmintr.mm"
include "syl22anc.mm"
include "cvv.mm"
include "setlikespec.mm"
include "trpredpred.mm"
include "syl.mm"
include "3adant1.mm"
include "eqssd.mm"

theorem trpredpo
  let cA: class A
  let cR: class R
  let cX: class X
  let vy: setvar y


  assert |- ( ( R Po A /\ X e. A /\ R Se A ) -> TrPred ( R , A , X ) = Pred ( R , A , X ) )

  proof
    cA
    cR
    wpo
    #
    cX
    cA
    wcel
    #
    cA
    cR
    wse
    #
    w3a
    #
    cA
    cR
    cX
    ctrpred
    #
    cA
    cR
    cX
    cpred
    #
    @3
    @1
    @2
    cA
    cR
    vy
    cv
    #
    cpred
    @5
    wss
    #
    vy
    @5
    wral
    #
    @5
    @5
    wss
    #
    @4
    @5
    wss
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @0
    @1
    @8
    @2
    @0
    @1
    wa
    @7
    vy
    @5
    cA
    cR
    cX
    @6
    predpo
    ralrimiv
    3adant3
    @9
    @3
    @5
    ssid
    a1i
    vy
    cA
    @5
    cR
    cX
    trpredmintr
    syl22anc
    @1
    @2
    @5
    @4
    wss
    #
    @0
    @1
    @2
    wa
    @5
    cvv
    wcel
    @10
    cA
    cR
    cX
    setlikespec
    cA
    cvv
    cR
    cX
    trpredpred
    syl
    3adant1
    eqssd
end
