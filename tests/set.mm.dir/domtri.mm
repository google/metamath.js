include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "wb.mm"
include "numth3.mm"
include "domtri2.mm"
include "syl2an.mm"

theorem domtri
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ~<_ B <-> -. B ~< A ) )

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
    cB
    cdom
    wbr
    cB
    cA
    csdm
    wbr
    wn
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
    domtri2
    syl2an
end
