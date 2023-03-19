include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "csdm.mm"
include "cun.mm"
include "simprl.mm"
include "domsdomtr.mm"
include "sylan.mm"
include "unfi2.mm"
include "sylancom.mm"
include "simpllr.mm"
include "sdomdomtr.mm"
include "syl2anc.mm"
include "wn.mm"
include "wb.mm"
include "con0.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "simpll.mm"
include "sdomdom.mm"
include "ad2antll.mm"
include "numdom.mm"
include "domtri2.mm"
include "sylancr.mm"
include "biimpar.mm"
include "cen.mm"
include "uncom.mm"
include "adantr.mm"
include "simpr.mm"
include "infunabs.mm"
include "syl3anc.mm"
include "syl5eqbr.mm"
include "simplrr.mm"
include "ensdomtr.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem infunsdom1
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( ( ( X e. dom card /\ _om ~<_ X ) /\ ( A ~<_ B /\ B ~< X ) ) -> ( A u. B ) ~< X )

  proof
    cX
    ccrd
    cdm
    #
    wcel
    #
    com
    cX
    cdom
    wbr
    #
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cB
    cX
    csdm
    wbr
    #
    wa
    #
    wa
    #
    cB
    com
    csdm
    wbr
    #
    cA
    cB
    cun
    #
    cX
    csdm
    wbr
    #
    @7
    @8
    wa
    @9
    com
    csdm
    wbr
    #
    @2
    @10
    @7
    @8
    cA
    com
    csdm
    wbr
    #
    @11
    @7
    @4
    @8
    @12
    @3
    @4
    @5
    simprl
    #
    cA
    cB
    com
    domsdomtr
    sylan
    cA
    cB
    unfi2
    sylancom
    @1
    @2
    @6
    @8
    simpllr
    @9
    com
    cX
    sdomdomtr
    syl2anc
    @7
    @8
    wn
    #
    com
    cB
    cdom
    wbr
    #
    @10
    @7
    @15
    @14
    @7
    com
    @0
    wcel
    #
    cB
    @0
    wcel
    #
    @15
    @14
    wb
    com
    con0
    wcel
    @16
    omelon
    com
    onenon
    ax-mp
    @7
    @1
    cB
    cX
    cdom
    wbr
    #
    @17
    @1
    @2
    @6
    simpll
    @5
    @18
    @3
    @4
    cB
    cX
    sdomdom
    ad2antll
    cX
    cB
    numdom
    syl2anc
    #
    com
    cB
    domtri2
    sylancr
    biimpar
    @7
    @15
    wa
    #
    @9
    cB
    cen
    wbr
    @5
    @10
    @20
    @9
    cB
    cA
    cun
    #
    cB
    cen
    cA
    cB
    uncom
    @20
    @17
    @15
    @4
    @21
    cB
    cen
    wbr
    @7
    @17
    @15
    @19
    adantr
    @7
    @15
    simpr
    @7
    @4
    @15
    @13
    adantr
    cB
    cA
    infunabs
    syl3anc
    syl5eqbr
    @3
    @4
    @5
    @15
    simplrr
    @9
    cB
    cX
    ensdomtr
    syl2anc
    syldan
    pm2.61dan
end
