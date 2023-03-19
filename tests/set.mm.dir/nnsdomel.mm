include "com.mm"
include "wcel.mm"
include "wa.mm"
include "ccrd.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "cardnn.mm"
include "eleq12.mm"
include "syl2an.mm"
include "cdm.mm"
include "con0.mm"
include "nnon.mm"
include "onenon.mm"
include "syl.mm"
include "cardsdom2.mm"
include "bitr3d.mm"

theorem nnsdomel
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A e. B <-> A ~< B ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cB
    csdm
    wbr
    #
    @0
    @2
    cA
    wceq
    @3
    cB
    wceq
    @4
    @5
    wb
    @1
    cA
    cardnn
    cB
    cardnn
    @2
    cA
    @3
    cB
    eleq12
    syl2an
    @0
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    @7
    wcel
    #
    @4
    @6
    wb
    @1
    @0
    cA
    con0
    wcel
    @8
    cA
    nnon
    cA
    onenon
    syl
    @1
    cB
    con0
    wcel
    @9
    cB
    nnon
    cB
    onenon
    syl
    cA
    cB
    cardsdom2
    syl2an
    bitr3d
end
