include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "ccda.mm"
include "co.mm"
include "cun.mm"
include "cen.mm"
include "wss.mm"
include "unnum.mm"
include "3adant3.mm"
include "ssun2.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "cdadom2.mm"
include "syl.mm"
include "cdacomen.mm"
include "domentr.mm"
include "sylancl.mm"
include "simp3.mm"
include "ssun1.mm"
include "domtr.mm"
include "syl2anc.mm"
include "infcdaabs.mm"
include "syl3anc.mm"
include "uncdadom.mm"
include "sbth.mm"

theorem infcda
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card /\ _om ~<_ A ) -> ( A +c B ) ~~ ( A u. B ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    w3a
    #
    cA
    cB
    ccda
    co
    #
    cA
    cB
    cun
    #
    cdom
    wbr
    #
    @6
    @5
    cdom
    wbr
    #
    @5
    @6
    cen
    wbr
    @4
    @5
    @6
    cA
    ccda
    co
    #
    cdom
    wbr
    #
    @9
    @6
    cen
    wbr
    #
    @7
    @4
    @5
    cA
    @6
    ccda
    co
    #
    cdom
    wbr
    #
    @12
    @9
    cen
    wbr
    @10
    @4
    cB
    @6
    cdom
    wbr
    #
    @13
    @4
    @6
    @0
    wcel
    #
    cB
    @6
    wss
    @14
    @1
    @2
    @15
    @3
    cA
    cB
    unnum
    3adant3
    #
    cB
    cA
    ssun2
    cB
    @6
    @0
    ssdomg
    mpisyl
    cB
    @6
    cA
    cdadom2
    syl
    cA
    @6
    cdacomen
    @5
    @12
    @9
    domentr
    sylancl
    @4
    @15
    com
    @6
    cdom
    wbr
    #
    cA
    @6
    cdom
    wbr
    #
    @11
    @16
    @4
    @3
    @18
    @17
    @1
    @2
    @3
    simp3
    @4
    @15
    cA
    @6
    wss
    @18
    @16
    cA
    cB
    ssun1
    cA
    @6
    @0
    ssdomg
    mpisyl
    #
    com
    cA
    @6
    domtr
    syl2anc
    @19
    @6
    cA
    infcdaabs
    syl3anc
    @5
    @9
    @6
    domentr
    syl2anc
    @1
    @2
    @8
    @3
    cA
    cB
    @0
    @0
    uncdadom
    3adant3
    @5
    @6
    sbth
    syl2anc
end
