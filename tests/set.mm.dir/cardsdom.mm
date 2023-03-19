include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "wb.mm"
include "numth3.mm"
include "cardsdom2.mm"
include "syl2an.mm"

theorem cardsdom
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( ( card ` A ) e. ( card ` B ) <-> A ~< B ) )

  proof
    cA
    cV
    wcel
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @0
    wcel
    cA
    ccrd
    cfv
    cB
    ccrd
    cfv
    wcel
    cA
    cB
    csdm
    wbr
    wb
    cB
    cW
    wcel
    cA
    cV
    numth3
    cB
    cW
    numth3
    cA
    cB
    cardsdom2
    syl2an
end
