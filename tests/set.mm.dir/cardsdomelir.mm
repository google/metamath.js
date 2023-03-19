include "ccrd.mm"
include "cfv.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "wn.mm"
include "csdm.mm"
include "con0.mm"
include "wss.mm"
include "cardon.mm"
include "onelssi.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "cdm.mm"
include "elfvdm.mm"
include "cardid2.mm"
include "syl.mm"
include "domentr.mm"
include "syl2anc.mm"
include "cardne.mm"
include "brsdom.mm"
include "sylanbrc.mm"

theorem cardsdomelir
  let cA: class A
  let cB: class B


  assert |- ( A e. ( card ` B ) -> A ~< B )

  proof
    cA
    cB
    ccrd
    cfv
    #
    wcel
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    cen
    wbr
    wn
    cA
    cB
    csdm
    wbr
    @1
    cA
    @0
    cdom
    wbr
    #
    @0
    cB
    cen
    wbr
    #
    @2
    @0
    con0
    wcel
    @1
    cA
    @0
    wss
    @3
    cB
    cardon
    #
    @0
    cA
    @5
    onelssi
    cA
    @0
    con0
    ssdomg
    mpsyl
    @1
    cB
    ccrd
    cdm
    wcel
    @4
    cA
    cB
    ccrd
    elfvdm
    cB
    cardid2
    syl
    cA
    @0
    cB
    domentr
    syl2anc
    cA
    cB
    cardne
    cA
    cB
    brsdom
    sylanbrc
end
