include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cale.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "ccrd.mm"
include "cdm.mm"
include "wb.mm"
include "simpl.mm"
include "alephon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "cardsdomel.mm"
include "sylancl.mm"
include "alephcard.mm"
include "eleq2i.mm"
include "syl6rbb.mm"

theorem alephsdom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A e. ( aleph ` B ) <-> A ~< ( aleph ` B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    cale
    cfv
    #
    csdm
    wbr
    #
    cA
    @3
    ccrd
    cfv
    #
    wcel
    #
    cA
    @3
    wcel
    @2
    @0
    @3
    ccrd
    cdm
    wcel
    #
    @4
    @6
    wb
    @0
    @1
    simpl
    @3
    con0
    wcel
    @7
    cB
    alephon
    @3
    onenon
    ax-mp
    cA
    @3
    cardsdomel
    sylancl
    @5
    @3
    cA
    cB
    alephcard
    eleq2i
    syl6rbb
end
