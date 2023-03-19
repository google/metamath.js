include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "cen.mm"
include "infxpdom.mm"
include "3expa.mm"
include "adantrl.mm"
include "simpll.mm"
include "numdom.mm"
include "ad2ant2rl.mm"
include "simprl.mm"
include "xpdom3.mm"
include "syl3anc.mm"
include "sbth.mm"
include "syl2anc.mm"

theorem infxpabs
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. dom card /\ _om ~<_ A ) /\ ( B =/= (/) /\ B ~<_ A ) ) -> ( A X. B ) ~~ A )

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
    wa
    #
    cB
    c0
    wne
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cxp
    #
    cA
    cdom
    wbr
    #
    cA
    @8
    cdom
    wbr
    #
    @8
    cA
    cen
    wbr
    @3
    @5
    @9
    @4
    @1
    @2
    @5
    @9
    cA
    cB
    infxpdom
    3expa
    adantrl
    @7
    @1
    cB
    @0
    wcel
    #
    @4
    @10
    @1
    @2
    @6
    simpll
    @1
    @5
    @11
    @2
    @4
    cA
    cB
    numdom
    ad2ant2rl
    @3
    @4
    @5
    simprl
    cA
    cB
    @0
    @0
    xpdom3
    syl3anc
    @8
    cA
    sbth
    syl2anc
end
