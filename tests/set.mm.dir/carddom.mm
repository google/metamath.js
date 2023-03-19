include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfv.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "wb.mm"
include "numth3.mm"
include "carddom2.mm"
include "syl2an.mm"

theorem carddom
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( ( card ` A ) C_ ( card ` B ) <-> A ~<_ B ) )

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
    wss
    cA
    cB
    cdom
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
    carddom2
    syl2an
end
