include "ccnv.mm"
include "cdm.mm"
include "cima.mm"
include "crn.mm"
include "imadmrn.mm"
include "df-rn.mm"
include "imaeq2i.mm"
include "dfdm4.mm"
include "3eqtr4i.mm"

theorem cnvimarndm
  let cA: class A


  assert |- ( `' A " ran A ) = dom A

  proof
    cA
    ccnv
    #
    @0
    cdm
    #
    cima
    @0
    crn
    @0
    cA
    crn
    #
    cima
    cA
    cdm
    @0
    imadmrn
    @2
    @1
    @0
    cA
    df-rn
    imaeq2i
    cA
    dfdm4
    3eqtr4i
end
