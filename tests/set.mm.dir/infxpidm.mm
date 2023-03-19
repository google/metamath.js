include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cxp.mm"
include "cen.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "numth3.mm"
include "syl.mm"
include "infxpidm2.mm"
include "mpancom.mm"

theorem infxpidm
  let cA: class A


  assert |- ( _om ~<_ A -> ( A X. A ) ~~ A )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    cA
    cA
    cxp
    cA
    cen
    wbr
    @1
    cA
    cvv
    wcel
    @0
    com
    cA
    cdom
    reldom
    brrelex2i
    cA
    cvv
    numth3
    syl
    cA
    infxpidm2
    mpancom
end
