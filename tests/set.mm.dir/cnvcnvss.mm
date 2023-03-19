include "ccnv.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cnvcnv.mm"
include "inss1.mm"
include "eqsstri.mm"

theorem cnvcnvss
  let cA: class A


  assert |- `' `' A C_ A

  proof
    cA
    ccnv
    ccnv
    cA
    cvv
    cvv
    cxp
    #
    cin
    cA
    cA
    cnvcnv
    cA
    @0
    inss1
    eqsstri
end
