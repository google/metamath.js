include "ccnv.mm"
include "cdif.mm"
include "cdm.mm"
include "c0.mm"
include "wceq.mm"
include "crn.mm"
include "dmnonrel.mm"
include "dm0rn0.mm"
include "mpbi.mm"

theorem rnnonrel
  let cA: class A


  assert |- ran ( A \ `' `' A ) = (/)

  proof
    cA
    cA
    ccnv
    ccnv
    cdif
    #
    cdm
    c0
    wceq
    @0
    crn
    c0
    wceq
    cA
    dmnonrel
    @0
    dm0rn0
    mpbi
end
