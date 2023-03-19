include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ccda.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "cdadom3.mm"
include "syl2anc.mm"
include "domtr.mm"
include "mpdan.mm"
include "c0.mm"
include "wne.mm"
include "infn0.mm"
include "wa.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "cdafn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "necon1ai.mm"
include "simpld.mm"
include "syl.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wex.mm"
include "ovex.mm"
include "domen.mm"
include "csn.mm"
include "cin.mm"
include "c1o.mm"
include "cun.mm"
include "indi.mm"
include "simprr.mm"
include "simpl.mm"
include "cdaval.mm"
include "sseqtrd.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "ensym.mm"
include "ad2antrl.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "wo.mm"
include "cdainflem.mm"
include "snex.mm"
include "xpexg.mm"
include "mpan2.mm"
include "inss2.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "0ex.mm"
include "xpsneng.mm"
include "domentr.mm"
include "domen1.mm"
include "syl5ibcom.mm"
include "con0.mm"
include "1on.mm"
include "jaod.mm"
include "syl5.mm"
include "syld.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "mpcom.mm"
include "impbii.mm"

theorem cdainf
  let cA: class A
  let vx: setvar x


  assert |- ( _om ~<_ A <-> _om ~<_ ( A +c A ) )

  proof
    com
    cA
    cdom
    wbr
    #
    com
    cA
    cA
    ccda
    co
    #
    cdom
    wbr
    #
    @0
    cA
    @1
    cdom
    wbr
    #
    @2
    @0
    cA
    cvv
    wcel
    #
    @4
    @3
    com
    cA
    cdom
    reldom
    brrelex2i
    #
    @5
    cA
    cA
    cvv
    cvv
    cdadom3
    syl2anc
    com
    cA
    @1
    domtr
    mpdan
    @4
    @2
    @0
    @2
    @1
    c0
    wne
    #
    @4
    @1
    infn0
    @6
    @4
    @4
    @4
    @4
    wa
    @1
    c0
    cA
    cA
    cvv
    ccda
    ccda
    cvv
    cvv
    cxp
    #
    wfn
    ccda
    cdm
    @7
    wceq
    cdafn
    @7
    ccda
    fndm
    ax-mp
    ndmov
    necon1ai
    simpld
    syl
    @2
    com
    vx
    cv
    #
    cen
    wbr
    #
    @8
    @1
    wss
    #
    wa
    #
    vx
    wex
    @4
    @0
    vx
    com
    @1
    cA
    cA
    ccda
    ovex
    domen
    @4
    @11
    @0
    vx
    @4
    @11
    @8
    cA
    c0
    csn
    #
    cxp
    #
    cin
    #
    @8
    cA
    c1o
    csn
    #
    cxp
    #
    cin
    #
    cun
    #
    com
    cen
    wbr
    #
    @0
    @4
    @11
    @19
    @4
    @11
    wa
    #
    @18
    @8
    com
    cen
    @20
    @18
    @8
    @13
    @16
    cun
    #
    cin
    #
    @8
    @8
    @13
    @16
    indi
    @20
    @8
    @21
    wss
    @22
    @8
    wceq
    @20
    @8
    @1
    @21
    @4
    @9
    @10
    simprr
    @20
    @4
    @4
    @1
    @21
    wceq
    @4
    @11
    simpl
    #
    @23
    cA
    cA
    cvv
    cvv
    cdaval
    syl2anc
    sseqtrd
    @8
    @21
    df-ss
    sylib
    syl5eqr
    @9
    @8
    com
    cen
    wbr
    @4
    @10
    com
    @8
    ensym
    ad2antrl
    eqbrtrd
    ex
    @19
    @14
    com
    cen
    wbr
    #
    @17
    com
    cen
    wbr
    #
    wo
    @4
    @0
    @14
    @17
    cdainflem
    @4
    @24
    @0
    @25
    @4
    @14
    cA
    cdom
    wbr
    #
    @24
    @0
    @4
    @14
    @13
    cdom
    wbr
    #
    @13
    cA
    cen
    wbr
    #
    @26
    @4
    @13
    cvv
    wcel
    #
    @14
    @13
    wss
    @27
    @4
    @12
    cvv
    wcel
    @29
    c0
    snex
    cA
    @12
    cvv
    cvv
    xpexg
    mpan2
    @8
    @13
    inss2
    @14
    @13
    cvv
    ssdomg
    mpisyl
    @4
    c0
    cvv
    wcel
    @28
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    mpan2
    @14
    @13
    cA
    domentr
    syl2anc
    @14
    com
    cA
    domen1
    syl5ibcom
    @4
    @17
    cA
    cdom
    wbr
    #
    @25
    @0
    @4
    @17
    @16
    cdom
    wbr
    #
    @16
    cA
    cen
    wbr
    #
    @30
    @4
    @16
    cvv
    wcel
    #
    @17
    @16
    wss
    @31
    @4
    @15
    cvv
    wcel
    @33
    c1o
    snex
    cA
    @15
    cvv
    cvv
    xpexg
    mpan2
    @8
    @16
    inss2
    @17
    @16
    cvv
    ssdomg
    mpisyl
    @4
    c1o
    con0
    wcel
    @32
    1on
    cA
    c1o
    cvv
    con0
    xpsneng
    mpan2
    @17
    @16
    cA
    domentr
    syl2anc
    @17
    com
    cA
    domen1
    syl5ibcom
    jaod
    syl5
    syld
    exlimdv
    syl5bi
    mpcom
    impbii
end
