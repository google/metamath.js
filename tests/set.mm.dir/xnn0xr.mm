include "cxnn0.mm"
include "wcel.mm"
include "cn0.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "cxr.mm"
include "elxnn0.mm"
include "nn0re.mm"
include "rexrd.mm"
include "pnfxr.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem xnn0xr
  let cA: class A


  assert |- ( A e. NN0* -> A e. RR* )

  proof
    cA
    cxnn0
    wcel
    cA
    cn0
    wcel
    #
    cA
    cpnf
    wceq
    #
    wo
    cA
    cxr
    wcel
    #
    cA
    elxnn0
    @0
    @2
    @1
    @0
    cA
    cA
    nn0re
    rexrd
    @1
    @2
    cpnf
    cxr
    wcel
    pnfxr
    cA
    cpnf
    cxr
    eleq1
    mpbiri
    jaoi
    sylbi
end
