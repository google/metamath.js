include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "cun.mm"
include "cen.mm"
include "ccda.mm"
include "co.mm"
include "cvv.mm"
include "simp1.mm"
include "reldom.mm"
include "brrelexi.mm"
include "3ad2ant3.mm"
include "uncdadom.mm"
include "syl2anc.mm"
include "infcdaabs.mm"
include "domentr.mm"
include "wss.mm"
include "unexg.mm"
include "ssun1.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "sbth.mm"

theorem infunabs
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ _om ~<_ A /\ B ~<_ A ) -> ( A u. B ) ~~ A )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    w3a
    #
    cA
    cB
    cun
    #
    cA
    cdom
    wbr
    #
    cA
    @5
    cdom
    wbr
    #
    @5
    cA
    cen
    wbr
    @4
    @5
    cA
    cB
    ccda
    co
    #
    cdom
    wbr
    #
    @8
    cA
    cen
    wbr
    @6
    @4
    @1
    cB
    cvv
    wcel
    #
    @9
    @1
    @2
    @3
    simp1
    #
    @3
    @1
    @10
    @2
    cB
    cA
    cdom
    reldom
    brrelexi
    3ad2ant3
    #
    cA
    cB
    @0
    cvv
    uncdadom
    syl2anc
    cA
    cB
    infcdaabs
    @5
    @8
    cA
    domentr
    syl2anc
    @4
    @5
    cvv
    wcel
    #
    cA
    @5
    wss
    @7
    @4
    @1
    @10
    @13
    @11
    @12
    cA
    cB
    @0
    cvv
    unexg
    syl2anc
    cA
    cB
    ssun1
    cA
    @5
    cvv
    ssdomg
    mpisyl
    @5
    cA
    sbth
    syl2anc
end
