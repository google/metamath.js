include "wf1.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "crn.mm"
include "wf1o.mm"
include "f1fn.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "f1orn.mm"
include "sylanbrc.mm"

theorem f1f1orn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> F : A -1-1-onto-> ran F )

  proof
    cA
    cB
    cF
    wf1
    #
    cF
    cA
    wfn
    cF
    ccnv
    wfun
    #
    cA
    cF
    crn
    cF
    wf1o
    cA
    cB
    cF
    f1fn
    @0
    cA
    cB
    cF
    wf
    @1
    cA
    cB
    cF
    df-f1
    simprbi
    cA
    cF
    f1orn
    sylanbrc
end
