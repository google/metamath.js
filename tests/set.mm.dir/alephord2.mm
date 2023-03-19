include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cale.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "alephord.mm"
include "ccrd.mm"
include "cdm.mm"
include "wb.mm"
include "alephon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "cardsdomel.mm"
include "mp2an.mm"
include "alephcard.mm"
include "eleq2i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem alephord2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A e. B <-> ( aleph ` A ) e. ( aleph ` B ) ) )

  proof
    cA
    con0
    wcel
    cB
    con0
    wcel
    wa
    cA
    cB
    wcel
    cA
    cale
    cfv
    #
    cB
    cale
    cfv
    #
    csdm
    wbr
    #
    @0
    @1
    wcel
    #
    cA
    cB
    alephord
    @2
    @0
    @1
    ccrd
    cfv
    #
    wcel
    #
    @3
    @0
    con0
    wcel
    @1
    ccrd
    cdm
    wcel
    #
    @2
    @5
    wb
    cA
    alephon
    @1
    con0
    wcel
    @6
    cB
    alephon
    @1
    onenon
    ax-mp
    @0
    @1
    cardsdomel
    mp2an
    @4
    @1
    @0
    cB
    alephcard
    eleq2i
    bitri
    syl6bb
end
