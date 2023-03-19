include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cale.mm"
include "cfv.mm"
include "wn.mm"
include "csdm.mm"
include "wbr.mm"
include "wss.mm"
include "cdom.mm"
include "wb.mm"
include "alephsdom.mm"
include "ancoms.mm"
include "notbid.mm"
include "word.mm"
include "alephon.mm"
include "onordi.mm"
include "eloni.mm"
include "ordtri1.mm"
include "sylancr.mm"
include "adantl.mm"
include "domtriord.mm"
include "mpan.mm"
include "3bitr4d.mm"

theorem alephdom2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( ( aleph ` A ) C_ B <-> ( aleph ` A ) ~<_ B ) )

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
    cB
    cA
    cale
    cfv
    #
    wcel
    #
    wn
    #
    cB
    @3
    csdm
    wbr
    #
    wn
    #
    @3
    cB
    wss
    #
    @3
    cB
    cdom
    wbr
    #
    @2
    @4
    @6
    @1
    @0
    @4
    @6
    wb
    cB
    cA
    alephsdom
    ancoms
    notbid
    @1
    @8
    @5
    wb
    #
    @0
    @1
    @3
    word
    cB
    word
    @10
    @3
    cA
    alephon
    #
    onordi
    cB
    eloni
    @3
    cB
    ordtri1
    sylancr
    adantl
    @1
    @9
    @7
    wb
    #
    @0
    @3
    con0
    wcel
    @1
    @12
    @11
    @3
    cB
    domtriord
    mpan
    adantl
    3bitr4d
end
