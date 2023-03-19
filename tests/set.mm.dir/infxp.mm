include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "csdm.mm"
include "cxp.mm"
include "cun.mm"
include "cen.mm"
include "sdomdom.mm"
include "wi.mm"
include "infxpabs.mm"
include "infunabs.mm"
include "3expa.mm"
include "adantrl.mm"
include "ensymd.mm"
include "entr.mm"
include "syl2anc.mm"
include "expr.mm"
include "syl5.mm"
include "wn.mm"
include "wb.mm"
include "domtri2.mm"
include "ad2ant2r.mm"
include "xpcomeng.mm"
include "adantr.mm"
include "simplrl.mm"
include "simplr.mm"
include "domtr.mm"
include "sylan.mm"
include "infn0.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "syl22anc.mm"
include "uncom.mm"
include "syl3anc.mm"
include "syl5eqbr.mm"
include "ex.mm"
include "sylbird.mm"
include "pm2.61d.mm"

theorem infxp
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. dom card /\ _om ~<_ A ) /\ ( B e. dom card /\ B =/= (/) ) ) -> ( A X. B ) ~~ ( A u. B ) )

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
    @0
    wcel
    #
    cB
    c0
    wne
    #
    wa
    #
    wa
    #
    cB
    cA
    csdm
    wbr
    #
    cA
    cB
    cxp
    #
    cA
    cB
    cun
    #
    cen
    wbr
    #
    @8
    cB
    cA
    cdom
    wbr
    #
    @7
    @11
    cB
    cA
    sdomdom
    @3
    @5
    @12
    @11
    wi
    @4
    @3
    @5
    @12
    @11
    @3
    @5
    @12
    wa
    wa
    #
    @9
    cA
    cen
    wbr
    cA
    @10
    cen
    wbr
    @11
    cA
    cB
    infxpabs
    @13
    @10
    cA
    @3
    @12
    @10
    cA
    cen
    wbr
    #
    @5
    @1
    @2
    @12
    @14
    cA
    cB
    infunabs
    3expa
    adantrl
    ensymd
    @9
    cA
    @10
    entr
    syl2anc
    expr
    adantrl
    syl5
    @7
    @8
    wn
    #
    cA
    cB
    cdom
    wbr
    #
    @11
    @1
    @4
    @16
    @15
    wb
    @2
    @5
    cA
    cB
    domtri2
    ad2ant2r
    @7
    @16
    @11
    @7
    @16
    wa
    #
    @9
    cB
    cA
    cxp
    #
    cen
    wbr
    #
    @18
    @10
    cen
    wbr
    #
    @11
    @7
    @19
    @16
    @1
    @4
    @19
    @2
    @5
    cA
    cB
    @0
    @0
    xpcomeng
    ad2ant2r
    adantr
    @17
    @18
    cB
    cen
    wbr
    #
    cB
    @10
    cen
    wbr
    @20
    @17
    @4
    com
    cB
    cdom
    wbr
    #
    cA
    c0
    wne
    #
    @16
    @21
    @3
    @4
    @5
    @16
    simplrl
    #
    @7
    @2
    @16
    @22
    @1
    @2
    @6
    simplr
    com
    cA
    cB
    domtr
    sylan
    #
    @2
    @23
    @1
    @6
    @16
    cA
    infn0
    ad3antlr
    @7
    @16
    simpr
    #
    cB
    cA
    infxpabs
    syl22anc
    @17
    @10
    cB
    @17
    @10
    cB
    cA
    cun
    #
    cB
    cen
    cA
    cB
    uncom
    @17
    @4
    @22
    @16
    @27
    cB
    cen
    wbr
    @24
    @25
    @26
    cB
    cA
    infunabs
    syl3anc
    syl5eqbr
    ensymd
    @18
    cB
    @10
    entr
    syl2anc
    @9
    @18
    @10
    entr
    syl2anc
    ex
    sylbird
    pm2.61d
end
