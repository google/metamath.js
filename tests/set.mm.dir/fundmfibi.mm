include "wfun.mm"
include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "dmfi.mm"
include "wfn.mm"
include "funfn.mm"
include "fnfi.mm"
include "sylanb.mm"
include "ex.mm"
include "impbid2.mm"

theorem fundmfibi
  let cF: class F


  assert |- ( Fun F -> ( F e. Fin <-> dom F e. Fin ) )

  proof
    cF
    wfun
    #
    cF
    cfn
    wcel
    #
    cF
    cdm
    #
    cfn
    wcel
    #
    cF
    dmfi
    @0
    @3
    @1
    @0
    cF
    @2
    wfn
    @3
    @1
    cF
    funfn
    @2
    cF
    fnfi
    sylanb
    ex
    impbid2
end
