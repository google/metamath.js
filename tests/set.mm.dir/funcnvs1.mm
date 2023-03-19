include "cs1.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cid.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "funcnvsn.mm"
include "df-s1.mm"
include "cnveqi.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem funcnvs1
  let cA: class A


  assert |- Fun `' <" A ">

  proof
    cA
    cs1
    #
    ccnv
    #
    wfun
    cc0
    cA
    cid
    cfv
    #
    cop
    csn
    #
    ccnv
    #
    wfun
    cc0
    @2
    funcnvsn
    @1
    @4
    @0
    @3
    cA
    df-s1
    cnveqi
    funeqi
    mpbir
end
