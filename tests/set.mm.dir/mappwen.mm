include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "c2o.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cen.mm"
include "simprr.mm"
include "pw2eng.mm"
include "ad2antrr.mm"
include "domentr.mm"
include "syl2anc.mm"
include "mapdom1.mm"
include "syl.mm"
include "cxp.mm"
include "con0.mm"
include "2on.mm"
include "a1i.mm"
include "simpll.mm"
include "mapxpen.mm"
include "syl3anc.mm"
include "elexi.mm"
include "enref.mm"
include "infxpidm2.mm"
include "adantr.mm"
include "mapen.mm"
include "sylancr.mm"
include "entr.mm"
include "ensymd.mm"
include "ad2antrl.mm"
include "endomtr.mm"
include "sbth.mm"

theorem mappwen
  let cA: class A
  let cB: class B


  assert |- ( ( ( B e. dom card /\ _om ~<_ B ) /\ ( 2o ~<_ A /\ A ~<_ ~P B ) ) -> ( A ^m B ) ~~ ~P B )

  proof
    cB
    ccrd
    cdm
    #
    wcel
    #
    com
    cB
    cdom
    wbr
    #
    wa
    #
    c2o
    cA
    cdom
    wbr
    #
    cA
    cB
    cpw
    #
    cdom
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cmap
    co
    #
    @5
    cdom
    wbr
    #
    @5
    @9
    cdom
    wbr
    #
    @9
    @5
    cen
    wbr
    @8
    @9
    c2o
    cB
    cmap
    co
    #
    cB
    cmap
    co
    #
    cdom
    wbr
    #
    @13
    @5
    cen
    wbr
    #
    @10
    @8
    cA
    @12
    cdom
    wbr
    #
    @14
    @8
    @6
    @5
    @12
    cen
    wbr
    #
    @16
    @3
    @4
    @6
    simprr
    @1
    @17
    @2
    @7
    cB
    @0
    pw2eng
    ad2antrr
    #
    cA
    @5
    @12
    domentr
    syl2anc
    cA
    @12
    cB
    mapdom1
    syl
    @8
    @13
    @12
    cen
    wbr
    #
    @12
    @5
    cen
    wbr
    @15
    @8
    @13
    c2o
    cB
    cB
    cxp
    #
    cmap
    co
    #
    cen
    wbr
    #
    @21
    @12
    cen
    wbr
    #
    @19
    @8
    c2o
    con0
    wcel
    #
    @1
    @1
    @22
    @24
    @8
    2on
    a1i
    @1
    @2
    @7
    simpll
    #
    @25
    c2o
    cB
    cB
    con0
    @0
    @0
    mapxpen
    syl3anc
    @8
    c2o
    c2o
    cen
    wbr
    @20
    cB
    cen
    wbr
    #
    @23
    c2o
    c2o
    con0
    2on
    elexi
    enref
    @3
    @26
    @7
    cB
    infxpidm2
    adantr
    c2o
    c2o
    @20
    cB
    mapen
    sylancr
    @13
    @21
    @12
    entr
    syl2anc
    @8
    @5
    @12
    @18
    ensymd
    @13
    @12
    @5
    entr
    syl2anc
    @9
    @13
    @5
    domentr
    syl2anc
    @8
    @17
    @12
    @9
    cdom
    wbr
    #
    @11
    @18
    @4
    @27
    @3
    @6
    c2o
    cA
    cB
    mapdom1
    ad2antrl
    @5
    @12
    @9
    endomtr
    syl2anc
    @9
    @5
    sbth
    syl2anc
end
