include "cun.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cpred.mm"
include "indir.mm"
include "df-pred.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem predun
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- Pred ( R , ( A u. B ) , X ) = ( Pred ( R , A , X ) u. Pred ( R , B , X ) )

  proof
    cA
    cB
    cun
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
    cun
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
    cun
    cA
    cB
    @1
    indir
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
    uneq12i
    3eqtr4i
end
