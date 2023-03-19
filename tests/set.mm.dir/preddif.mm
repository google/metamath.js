include "cdif.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cpred.mm"
include "indifdir.mm"
include "df-pred.mm"
include "difeq12i.mm"
include "3eqtr4i.mm"

theorem preddif
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- Pred ( R , ( A \ B ) , X ) = ( Pred ( R , A , X ) \ Pred ( R , B , X ) )

  proof
    cA
    cB
    cdif
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
    cdif
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
    cdif
    cA
    cB
    @1
    indifdir
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
    difeq12i
    3eqtr4i
end
