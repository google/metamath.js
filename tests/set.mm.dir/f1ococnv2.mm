include "wf1o.mm"
include "wfo.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "f1ofo.mm"
include "fococnv2.mm"
include "syl.mm"

theorem f1ococnv2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> ( F o. `' F ) = ( _I |` B ) )

  proof
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wfo
    cF
    cF
    ccnv
    ccom
    cid
    cB
    cres
    wceq
    cA
    cB
    cF
    f1ofo
    cA
    cB
    cF
    fococnv2
    syl
end
