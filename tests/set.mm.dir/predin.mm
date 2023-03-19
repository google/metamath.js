include "cin.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cpred.mm"
include "inindir.mm"
include "df-pred.mm"
include "ineq12i.mm"
include "3eqtr4i.mm"

theorem predin
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- Pred ( R , ( A i^i B ) , X ) = ( Pred ( R , A , X ) i^i Pred ( R , B , X ) )

  proof
    cA
    cB
    cin
    #
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    cA
    @1
    cin
    #
    cB
    @1
    cin
    #
    cin
    @0
    cR
    cX
    cpred
    cA
    cR
    cX
    cpred
    #
    cB
    cR
    cX
    cpred
    #
    cin
    cA
    cB
    @1
    inindir
    @0
    cR
    cX
    df-pred
    @4
    @2
    @5
    @3
    cA
    cR
    cX
    df-pred
    cB
    cR
    cX
    df-pred
    ineq12i
    3eqtr4i
end
