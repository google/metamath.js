include "ccnv.mm"
include "crn.mm"
include "cvv.mm"
include "cres.mm"
include "cnvcnv2.mm"
include "rneqi.mm"
include "rncnvcnv.mm"
include "eqtr3i.mm"

theorem rnresv
  let cA: class A


  assert |- ran ( A |` _V ) = ran A

  proof
    cA
    ccnv
    ccnv
    #
    crn
    cA
    cvv
    cres
    #
    crn
    cA
    crn
    @0
    @1
    cA
    cnvcnv2
    rneqi
    cA
    rncnvcnv
    eqtr3i
end
