include "wf1.mm"
include "crn.mm"
include "wf1o.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "f1f1orn.mm"
include "f1ococnv1.mm"
include "syl.mm"

theorem f1cocnv1
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> ( `' F o. F ) = ( _I |` A ) )

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
    cF
    ccnv
    cF
    ccom
    cid
    cA
    cres
    wceq
    cA
    cB
    cF
    f1f1orn
    cA
    @0
    cF
    f1ococnv1
    syl
end
