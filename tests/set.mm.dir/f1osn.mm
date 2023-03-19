include "csn.mm"
include "cop.mm"
include "wf1o.mm"
include "wfn.mm"
include "ccnv.mm"
include "fnsn.mm"
include "cnvsn.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "dff1o4.mm"
include "mpbir2an.mm"

theorem f1osn
  let cA: class A
  let cB: class B
  assume f1osn.1: |- A e. _V
  assume f1osn.2: |- B e. _V


  assert |- { <. A , B >. } : { A } -1-1-onto-> { B }

  proof
    cA
    csn
    #
    cB
    csn
    #
    cA
    cB
    cop
    csn
    #
    wf1o
    @2
    @0
    wfn
    @2
    ccnv
    #
    @1
    wfn
    #
    cA
    cB
    f1osn.1
    f1osn.2
    fnsn
    @4
    cB
    cA
    cop
    csn
    #
    @1
    wfn
    cB
    cA
    f1osn.2
    f1osn.1
    fnsn
    @1
    @3
    @5
    cA
    cB
    f1osn.1
    f1osn.2
    cnvsn
    fneq1i
    mpbir
    @0
    @1
    @2
    dff1o4
    mpbir2an
end
