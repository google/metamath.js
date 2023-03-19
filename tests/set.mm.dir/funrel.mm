include "wfun.mm"
include "wrel.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "wss.mm"
include "df-fun.mm"
include "simplbi.mm"

theorem funrel
  let cA: class A


  assert |- ( Fun A -> Rel A )

  proof
    cA
    wfun
    cA
    wrel
    cA
    cA
    ccnv
    ccom
    cid
    wss
    cA
    df-fun
    simplbi
end
