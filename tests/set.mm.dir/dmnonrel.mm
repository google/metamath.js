include "ccnv.mm"
include "cdif.mm"
include "cdm.mm"
include "crn.mm"
include "c0.mm"
include "dfdm4.mm"
include "cnvnonrel.mm"
include "rneqi.mm"
include "rn0.mm"
include "3eqtri.mm"

theorem dmnonrel
  let cA: class A


  assert |- dom ( A \ `' `' A ) = (/)

  proof
    cA
    cA
    ccnv
    ccnv
    cdif
    #
    cdm
    @0
    ccnv
    #
    crn
    c0
    crn
    c0
    @0
    dfdm4
    @1
    c0
    cA
    cnvnonrel
    rneqi
    rn0
    3eqtri
end
