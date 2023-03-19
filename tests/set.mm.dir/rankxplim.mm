include "cun.mm"
include "crnk.mm"
include "cfv.mm"
include "wlim.mm"
include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "csuc.mm"
include "wral.mm"
include "wcel.mm"
include "cpw.mm"
include "cpr.mm"
include "cuni.mm"
include "pwuni.mm"
include "vex.mm"
include "uniop.mm"
include "pweqi.mm"
include "sseqtri.mm"
include "unipr.mm"
include "sspwb.mm"
include "mpbi.mm"
include "sstri.mm"
include "unex.mm"
include "pwex.mm"
include "rankss.mm"
include "ax-mp.mm"
include "rankel.mm"
include "rankelun.mm"
include "syl2an.mm"
include "adantl.mm"
include "wb.mm"
include "ranklim.mm"
include "bitrd.mm"
include "adantr.mm"
include "mpbid.mm"
include "con0.mm"
include "wi.mm"
include "rankon.mm"
include "ontr2.mm"
include "mp2an.mm"
include "sylancr.mm"
include "onsucssi.mm"
include "sylib.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "fveq2.mm"
include "suceq.mm"
include "syl.mm"
include "sseq1d.mm"
include "ralxp.mm"
include "xpex.mm"
include "rankbnd.mm"
include "bitr3i.mm"
include "rankxpl.mm"
include "eqssd.mm"

theorem rankxplim
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rankxplim.1: |- A e. _V
  assume rankxplim.2: |- B e. _V


  assert |- ( ( Lim ( rank ` ( A u. B ) ) /\ ( A X. B ) =/= (/) ) -> ( rank ` ( A X. B ) ) = ( rank ` ( A u. B ) ) )

  proof
    cA
    cB
    cun
    #
    crnk
    cfv
    #
    wlim
    #
    cA
    cB
    cxp
    #
    c0
    wne
    #
    wa
    @3
    crnk
    cfv
    #
    @1
    @2
    @5
    @1
    wss
    #
    @4
    @2
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    crnk
    cfv
    #
    csuc
    #
    @1
    wss
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    @6
    @2
    @12
    vx
    vy
    cA
    cB
    @2
    @7
    cA
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    #
    wa
    #
    @10
    @1
    wcel
    #
    @12
    @17
    @10
    @7
    @8
    cun
    #
    cpw
    #
    cpw
    #
    crnk
    cfv
    #
    wss
    #
    @22
    @1
    wcel
    #
    @18
    @9
    @21
    wss
    @23
    @9
    @7
    @8
    cpr
    #
    cpw
    #
    @21
    @9
    @9
    cuni
    #
    cpw
    @26
    @9
    pwuni
    @27
    @25
    @7
    @8
    vx
    vex
    #
    vy
    vex
    #
    uniop
    pweqi
    sseqtri
    @25
    @20
    wss
    @26
    @21
    wss
    @25
    @25
    cuni
    #
    cpw
    @20
    @25
    pwuni
    @30
    @19
    @7
    @8
    @28
    @29
    unipr
    pweqi
    sseqtri
    @25
    @20
    sspwb
    mpbi
    sstri
    @9
    @21
    @20
    @19
    @7
    @8
    @28
    @29
    unex
    pwex
    pwex
    rankss
    ax-mp
    @17
    @19
    crnk
    cfv
    @1
    wcel
    #
    @24
    @16
    @31
    @2
    @14
    @7
    crnk
    cfv
    cA
    crnk
    cfv
    wcel
    @8
    crnk
    cfv
    cB
    crnk
    cfv
    wcel
    @31
    @15
    @7
    cA
    rankxplim.1
    rankel
    @8
    cB
    rankxplim.2
    rankel
    @7
    @8
    cA
    cB
    @28
    @29
    rankxplim.1
    rankxplim.2
    rankelun
    syl2an
    adantl
    @2
    @31
    @24
    wb
    @16
    @2
    @31
    @20
    crnk
    cfv
    @1
    wcel
    @24
    @19
    @1
    ranklim
    @20
    @1
    ranklim
    bitrd
    adantr
    mpbid
    @10
    con0
    wcel
    @1
    con0
    wcel
    @23
    @24
    wa
    @18
    wi
    @9
    rankon
    #
    @0
    rankon
    #
    @10
    @22
    @1
    ontr2
    mp2an
    sylancr
    @10
    @1
    @32
    @33
    onsucssi
    sylib
    ralrimivva
    @13
    vz
    cv
    #
    crnk
    cfv
    #
    csuc
    #
    @1
    wss
    #
    vz
    @3
    wral
    @6
    @37
    @12
    vz
    vx
    vy
    cA
    cB
    @34
    @9
    wceq
    #
    @36
    @11
    @1
    @38
    @35
    @10
    wceq
    @36
    @11
    wceq
    @34
    @9
    crnk
    fveq2
    @35
    @10
    suceq
    syl
    sseq1d
    ralxp
    vz
    @3
    @1
    cA
    cB
    rankxplim.1
    rankxplim.2
    xpex
    rankbnd
    bitr3i
    sylib
    adantr
    @4
    @1
    @5
    wss
    @2
    cA
    cB
    rankxplim.1
    rankxplim.2
    rankxpl
    adantl
    eqssd
end
