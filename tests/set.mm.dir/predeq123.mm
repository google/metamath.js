include "wceq.mm"
include "w3a.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cpred.mm"
include "simp2.mm"
include "cnveq.mm"
include "3ad2ant1.mm"
include "sneq.mm"
include "3ad2ant3.mm"
include "imaeq12d.mm"
include "ineq12d.mm"
include "df-pred.mm"
include "3eqtr4g.mm"

theorem predeq123
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y


  assert |- ( ( R = S /\ A = B /\ X = Y ) -> Pred ( R , A , X ) = Pred ( S , B , Y ) )

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
    csn
    #
    cima
    #
    cin
    cB
    cS
    ccnv
    #
    cY
    csn
    #
    cima
    #
    cin
    cA
    cR
    cX
    cpred
    cB
    cS
    cY
    cpred
    @3
    cA
    cB
    @6
    @9
    @0
    @1
    @2
    simp2
    @3
    @4
    @7
    @5
    @8
    @0
    @1
    @4
    @7
    wceq
    @2
    cR
    cS
    cnveq
    3ad2ant1
    @2
    @0
    @5
    @8
    wceq
    @1
    cX
    cY
    sneq
    3ad2ant3
    imaeq12d
    ineq12d
    cA
    cR
    cX
    df-pred
    cB
    cS
    cY
    df-pred
    3eqtr4g
end
