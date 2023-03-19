include "cpred.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "df-pred.mm"
include "inidm.mm"
include "ineq2i.mm"
include "eqtr4i.mm"
include "inass.mm"
include "ineq1i.mm"

theorem predidm
  let cA: class A
  let cR: class R
  let cX: class X


  assert |- Pred ( R , Pred ( R , A , X ) , X ) = Pred ( R , A , X )

  proof
    cA
    cR
    cX
    cpred
    #
    cR
    cX
    cpred
    @0
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    #
    @0
    @0
    cR
    cX
    df-pred
    @0
    cA
    @1
    cin
    #
    @1
    cin
    #
    @2
    @0
    cA
    @1
    @1
    cin
    #
    cin
    #
    @4
    @0
    @3
    @6
    cA
    cR
    cX
    df-pred
    #
    @5
    @1
    cA
    @1
    inidm
    ineq2i
    eqtr4i
    cA
    @1
    @1
    inass
    eqtr4i
    @0
    @3
    @1
    @7
    ineq1i
    eqtr4i
    eqtr4i
end
