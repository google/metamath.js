include "cxnn0.mm"
include "wcel.mm"
include "cn0.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "cmnf.mm"
include "wne.mm"
include "elxnn0.mm"
include "nn0re.mm"
include "renemnfd.mm"
include "pnfnemnf.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem xnn0nemnf
  let cA: class A


  assert |- ( A e. NN0* -> A =/= -oo )

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
    cmnf
    wne
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
    renemnfd
    @1
    @2
    cpnf
    cmnf
    wne
    pnfnemnf
    cA
    cpnf
    cmnf
    neeq1
    mpbiri
    jaoi
    sylbi
end
