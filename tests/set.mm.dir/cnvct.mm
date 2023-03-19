include "ccnv.mm"
include "cdom.mm"
include "wbr.mm"
include "com.mm"
include "cen.mm"
include "wrel.mm"
include "cvv.mm"
include "wcel.mm"
include "relcnv.mm"
include "ctex.mm"
include "cnvexg.mm"
include "syl.mm"
include "cnven.mm"
include "sylancr.mm"
include "wss.mm"
include "cnvcnvss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "domtr.mm"
include "mpancom.mm"

theorem cnvct
  let cA: class A


  assert |- ( A ~<_ _om -> `' A ~<_ _om )

  proof
    cA
    ccnv
    #
    cA
    cdom
    wbr
    #
    cA
    com
    cdom
    wbr
    #
    @0
    com
    cdom
    wbr
    @2
    @0
    @0
    ccnv
    #
    cen
    wbr
    #
    @3
    cA
    cdom
    wbr
    #
    @1
    @2
    @0
    wrel
    @0
    cvv
    wcel
    #
    @4
    cA
    relcnv
    @2
    cA
    cvv
    wcel
    #
    @6
    cA
    ctex
    #
    cA
    cvv
    cnvexg
    syl
    @0
    cvv
    cnven
    sylancr
    @2
    @7
    @3
    cA
    wss
    @5
    @8
    cA
    cnvcnvss
    @3
    cA
    cvv
    ssdomg
    mpisyl
    @0
    @3
    cA
    endomtr
    syl2anc
    @0
    cA
    com
    domtr
    mpancom
end
