include "cfn.mm"
include "wcel.mm"
include "ccnv.mm"
include "cen.mm"
include "wbr.mm"
include "wss.mm"
include "cnvcnvss.mm"
include "ssfi.mm"
include "mpan2.mm"
include "wrel.mm"
include "cvv.mm"
include "relcnv.mm"
include "cnvexg.mm"
include "cnven.mm"
include "sylancr.mm"
include "enfii.mm"
include "syl2anc.mm"

theorem cnvfi
  let cA: class A


  assert |- ( A e. Fin -> `' A e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cA
    ccnv
    #
    ccnv
    #
    cfn
    wcel
    #
    @1
    @2
    cen
    wbr
    #
    @1
    cfn
    wcel
    @0
    @2
    cA
    wss
    @3
    cA
    cnvcnvss
    cA
    @2
    ssfi
    mpan2
    @0
    @1
    wrel
    @1
    cvv
    wcel
    @4
    cA
    relcnv
    cA
    cfn
    cnvexg
    @1
    cvv
    cnven
    sylancr
    @1
    @2
    enfii
    syl2anc
end
