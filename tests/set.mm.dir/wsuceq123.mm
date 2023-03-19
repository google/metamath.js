include "wceq.mm"
include "w3a.mm"
include "ccnv.mm"
include "cpred.mm"
include "cinf.mm"
include "cwsuc.mm"
include "simp1.mm"
include "cnveqd.mm"
include "predeq123.mm"
include "syld3an1.mm"
include "simp2.mm"
include "infeq123d.mm"
include "df-wsuc.mm"
include "3eqtr4g.mm"

theorem wsuceq123
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y


  assert |- ( ( R = S /\ A = B /\ X = Y ) -> wsuc ( R , A , X ) = wsuc ( S , B , Y ) )

  proof
    cR
    cS
    wceq
    #
    cA
    cB
    wceq
    #
    cX
    cY
    wceq
    #
    w3a
    #
    cA
    cR
    ccnv
    #
    cX
    cpred
    #
    cA
    cR
    cinf
    cB
    cS
    ccnv
    #
    cY
    cpred
    #
    cB
    cS
    cinf
    cA
    cR
    cX
    cwsuc
    cB
    cS
    cY
    cwsuc
    @3
    @5
    cA
    cR
    @7
    cB
    cS
    @4
    @6
    wceq
    @1
    @0
    @2
    @5
    @7
    wceq
    @3
    cR
    cS
    @0
    @1
    @2
    simp1
    #
    cnveqd
    cA
    cB
    @4
    @6
    cX
    cY
    predeq123
    syld3an1
    @0
    @1
    @2
    simp2
    @8
    infeq123d
    cA
    cR
    cX
    df-wsuc
    cB
    cS
    cY
    df-wsuc
    3eqtr4g
end
