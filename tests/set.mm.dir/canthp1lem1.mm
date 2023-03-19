include "c1o.mm"
include "csdm.mm"
include "wbr.mm"
include "c2o.mm"
include "ccda.mm"
include "co.mm"
include "cxp.mm"
include "cdom.mm"
include "cpw.mm"
include "1sdom2.mm"
include "cdaxpdom.mm"
include "mpan2.mm"
include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wex.mm"
include "sdom0.mm"
include "breq2.mm"
include "mtbiri.mm"
include "con2i.mm"
include "neq0.mm"
include "sylib.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cen.mm"
include "cvv.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "adantr.mm"
include "enrefg.mm"
include "syl.mm"
include "cpr.mm"
include "df2o2.mm"
include "pwpw0.mm"
include "eqtr4i.mm"
include "0ex.mm"
include "vex.mm"
include "en2sn.mm"
include "mp2an.mm"
include "pwen.mm"
include "ax-mp.mm"
include "eqbrtri.mm"
include "xpen.mm"
include "sylancl.mm"
include "snex.mm"
include "pwex.mm"
include "cun.mm"
include "uncom.mm"
include "wss.mm"
include "simpr.mm"
include "snssd.mm"
include "undif.mm"
include "syl5eq.mm"
include "difexg.mm"
include "canth2g.mm"
include "domunsn.mm"
include "3syl.mm"
include "eqbrtrrd.mm"
include "xpdom1g.mm"
include "sylancr.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "pwcdaen.mm"
include "ensymd.mm"
include "domentr.mm"
include "cin.mm"
include "a1i.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "cdaun.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "exlimddv.mm"
include "domtr.mm"

theorem canthp1lem1
  let cA: class A
  let vx: setvar x


  assert |- ( 1o ~< A -> ( A +c 2o ) ~<_ ~P A )

  proof
    c1o
    cA
    csdm
    wbr
    #
    cA
    c2o
    ccda
    co
    #
    cA
    c2o
    cxp
    #
    cdom
    wbr
    #
    @2
    cA
    cpw
    #
    cdom
    wbr
    #
    @1
    @4
    cdom
    wbr
    @0
    c1o
    c2o
    csdm
    wbr
    @3
    1sdom2
    cA
    c2o
    cdaxpdom
    mpan2
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @5
    vx
    @0
    cA
    c0
    wceq
    #
    wn
    @7
    vx
    wex
    @8
    @0
    @8
    @0
    c1o
    c0
    csdm
    wbr
    c1o
    sdom0
    cA
    c0
    c1o
    csdm
    breq2
    mtbiri
    con2i
    vx
    cA
    neq0
    sylib
    @0
    @7
    wa
    #
    @2
    cA
    @6
    csn
    #
    cdif
    #
    @10
    ccda
    co
    #
    cpw
    #
    cdom
    wbr
    #
    @13
    @4
    cen
    wbr
    #
    @5
    @9
    @2
    @11
    cpw
    #
    @10
    cpw
    #
    cxp
    #
    cdom
    wbr
    #
    @18
    @13
    cen
    wbr
    @14
    @9
    @2
    cA
    @17
    cxp
    #
    cen
    wbr
    #
    @20
    @18
    cdom
    wbr
    #
    @19
    @9
    cA
    cA
    cen
    wbr
    #
    c2o
    @17
    cen
    wbr
    @21
    @9
    cA
    cvv
    wcel
    #
    @23
    @0
    @24
    @7
    c1o
    cA
    csdm
    relsdom
    brrelex2i
    adantr
    #
    cA
    cvv
    enrefg
    syl
    c2o
    c0
    csn
    #
    cpw
    #
    @17
    cen
    c2o
    c0
    @26
    cpr
    @27
    df2o2
    pwpw0
    eqtr4i
    @26
    @10
    cen
    wbr
    #
    @27
    @17
    cen
    wbr
    c0
    cvv
    wcel
    @6
    cvv
    wcel
    @28
    0ex
    vx
    vex
    c0
    @6
    cvv
    cvv
    en2sn
    mp2an
    @26
    @10
    pwen
    ax-mp
    eqbrtri
    cA
    cA
    c2o
    @17
    xpen
    sylancl
    @9
    @17
    cvv
    wcel
    cA
    @16
    cdom
    wbr
    @22
    @10
    @6
    snex
    #
    pwex
    @9
    @11
    @10
    cun
    #
    cA
    @16
    cdom
    @9
    @30
    @10
    @11
    cun
    #
    cA
    @11
    @10
    uncom
    @9
    @10
    cA
    wss
    @31
    cA
    wceq
    @9
    @6
    cA
    @0
    @7
    simpr
    snssd
    @10
    cA
    undif
    sylib
    syl5eq
    #
    @9
    @11
    cvv
    wcel
    #
    @11
    @16
    csdm
    wbr
    @30
    @16
    cdom
    wbr
    @9
    @24
    @33
    @25
    cA
    @10
    cvv
    difexg
    syl
    #
    @11
    cvv
    canth2g
    @11
    @16
    @6
    domunsn
    3syl
    eqbrtrrd
    cA
    @16
    @17
    cvv
    xpdom1g
    sylancr
    @2
    @20
    @18
    endomtr
    syl2anc
    @9
    @13
    @18
    @9
    @33
    @10
    cvv
    wcel
    #
    @13
    @18
    cen
    wbr
    @34
    @29
    @11
    @10
    cvv
    cvv
    pwcdaen
    sylancl
    ensymd
    @2
    @18
    @13
    domentr
    syl2anc
    @9
    @12
    cA
    cen
    wbr
    @15
    @9
    @12
    @30
    cA
    cen
    @9
    @33
    @35
    @11
    @10
    cin
    #
    c0
    wceq
    #
    @12
    @30
    cen
    wbr
    @34
    @35
    @9
    @29
    a1i
    @37
    @9
    @36
    @10
    @11
    cin
    c0
    @11
    @10
    incom
    @10
    cA
    disjdif
    eqtri
    a1i
    @11
    @10
    cvv
    cvv
    cdaun
    syl3anc
    @32
    breqtrd
    @12
    cA
    pwen
    syl
    @2
    @13
    @4
    domentr
    syl2anc
    exlimddv
    @1
    @2
    @4
    domtr
    syl2anc
end
