include "cdm.mm"
include "ccnv.mm"
include "crn.mm"
include "dfdm4.mm"
include "df-rn.mm"
include "eqtr2i.mm"

theorem dmcnvcnv
  let cA: class A


  assert |- dom `' `' A = dom A

  proof
    cA
    cdm
    cA
    ccnv
    #
    crn
    @0
    ccnv
    cdm
    cA
    dfdm4
    @0
    df-rn
    eqtr2i
end
