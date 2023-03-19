include "wf1.mm"
include "wfun.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "crn.mm"
include "cres.mm"
include "wceq.mm"
include "f1fun.mm"
include "funcocnv2.mm"
include "syl.mm"

theorem f1cocnv2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> ( F o. `' F ) = ( _I |` ran F ) )

  proof
    cA
    cB
    cF
    wf1
    cF
    wfun
    cF
    cF
    ccnv
    ccom
    cid
    cF
    crn
    cres
    wceq
    cA
    cB
    cF
    f1fun
    cF
    funcocnv2
    syl
end
