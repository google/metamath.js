include "wf1o.mm"
include "ccnv.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"

theorem f1ocnvdm
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-onto-> B /\ C e. B ) -> ( `' F ` C ) e. A )

  proof
    cA
    cB
    cF
    wf1o
    #
    cB
    cA
    cC
    cF
    ccnv
    #
    @0
    cB
    cA
    @1
    wf1o
    cB
    cA
    @1
    wf
    cA
    cB
    cF
    f1ocnv
    cB
    cA
    @1
    f1of
    syl
    ffvelrnda
end
