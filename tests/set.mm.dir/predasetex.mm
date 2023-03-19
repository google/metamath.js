include "cpred.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cvv.mm"
include "df-pred.mm"
include "inex1.mm"
include "eqeltri.mm"

theorem predasetex
  let cA: class A
  let cR: class R
  let cX: class X
  assume predasetex.1: |- A e. _V


  assert |- Pred ( R , A , X ) e. _V

  proof
    cA
    cR
    cX
    cpred
    cA
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    cvv
    cA
    cR
    cX
    df-pred
    cA
    @0
    predasetex.1
    inex1
    eqeltri
end
