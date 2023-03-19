include "cpred.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "df-pred.mm"
include "inss1.mm"
include "eqsstri.mm"

theorem predss
  let cA: class A
  let cR: class R
  let cX: class X


  assert |- Pred ( R , A , X ) C_ A

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
    cA
    cA
    cR
    cX
    df-pred
    cA
    @0
    inss1
    eqsstri
end
