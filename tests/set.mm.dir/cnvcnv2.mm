include "ccnv.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "cnvcnv.mm"
include "df-res.mm"
include "eqtr4i.mm"

theorem cnvcnv2
  let cA: class A


  assert |- `' `' A = ( A |` _V )

  proof
    cA
    ccnv
    ccnv
    cA
    cvv
    cvv
    cxp
    cin
    cA
    cvv
    cres
    cA
    cnvcnv
    cA
    cvv
    df-res
    eqtr4i
end
