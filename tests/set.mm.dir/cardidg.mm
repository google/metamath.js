include "wcel.mm"
include "cvv.mm"
include "ccrd.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "elex.mm"
include "cdm.mm"
include "cardeqv.mm"
include "eleq2i.mm"
include "cardid2.mm"
include "sylbir.mm"
include "syl.mm"

theorem cardidg
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ( card ` A ) ~~ A )

  proof
    cA
    cB
    wcel
    cA
    cvv
    wcel
    #
    cA
    ccrd
    cfv
    cA
    cen
    wbr
    #
    cA
    cB
    elex
    @0
    cA
    ccrd
    cdm
    #
    wcel
    @1
    @2
    cvv
    cA
    cardeqv
    eleq2i
    cA
    cardid2
    sylbir
    syl
end
