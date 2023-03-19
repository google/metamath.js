include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "con0.mm"
include "cardon.mm"
include "cen.mm"
include "wb.mm"
include "cardid2.mm"
include "domen2.mm"
include "syl.mm"
include "biimpar.mm"
include "ondomen.mm"
include "sylancr.mm"

theorem numdom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B ~<_ A ) -> B e. dom card )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    cA
    ccrd
    cfv
    #
    con0
    wcel
    cB
    @3
    cdom
    wbr
    #
    cB
    @0
    wcel
    cA
    cardon
    @1
    @4
    @2
    @1
    @3
    cA
    cen
    wbr
    @4
    @2
    wb
    cA
    cardid2
    @3
    cA
    cB
    domen2
    syl
    biimpar
    @3
    cB
    ondomen
    sylancr
end
