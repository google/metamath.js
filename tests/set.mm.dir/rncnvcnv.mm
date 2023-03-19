include "crn.mm"
include "ccnv.mm"
include "cdm.mm"
include "df-rn.mm"
include "dfdm4.mm"
include "eqtr2i.mm"

theorem rncnvcnv
  let cA: class A


  assert |- ran `' `' A = ran A

  proof
    cA
    crn
    cA
    ccnv
    #
    cdm
    @0
    ccnv
    crn
    cA
    df-rn
    @0
    dfdm4
    eqtr2i
end
