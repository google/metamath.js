include "wf1.mm"
include "crn.mm"
include "wf1o.mm"
include "ccnv.mm"
include "f1f1orn.mm"
include "f1ocnv.mm"
include "syl.mm"

theorem f1cnv
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> `' F : ran F -1-1-onto-> A )

  proof
    cA
    cB
    cF
    wf1
    cA
    cF
    crn
    #
    cF
    wf1o
    @0
    cA
    cF
    ccnv
    wf1o
    cA
    cB
    cF
    f1f1orn
    cA
    @0
    cF
    f1ocnv
    syl
end
