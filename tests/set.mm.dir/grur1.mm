include "cgru.mm"
include "wcel.mm"
include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "wn.mm"
include "cv.mm"
include "crnk.mm"
include "wceq.mm"
include "wrex.mm"
include "wex.mm"
include "nss.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "ad2antrl.mm"
include "ctc.mm"
include "simplr.mm"
include "simprl.mm"
include "r1elssi.mm"
include "sseld.mm"
include "sylc.mm"
include "tcrank.mm"
include "syl.mm"
include "eleq2d.mm"
include "wtr.mm"
include "gruelss.mm"
include "grutr.mm"
include "adantr.mm"
include "cvv.mm"
include "vex.mm"
include "tcmin.mm"
include "ax-mp.mm"
include "syl2anc.mm"
include "wfun.mm"
include "wf.mm"
include "rankf.mm"
include "ffun.mm"
include "fvelima.mm"
include "mpan.mm"
include "ssrexv.mm"
include "syl2im.mm"
include "ad2ant2r.mm"
include "sylbid.mm"
include "wo.mm"
include "simprr.mm"
include "cdm.mm"
include "wb.mm"
include "cina.mm"
include "cwina.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "gruina.mm"
include "sylan2.mm"
include "inawina.mm"
include "winaon.mm"
include "3syl.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "syl6eleqr.mm"
include "rankr1ag.mm"
include "mtbid.mm"
include "w3o.mm"
include "rankon.mm"
include "word.mm"
include "eloni.mm"
include "ordtri3or.mm"
include "syl2an.mm"
include "sylancr.mm"
include "3orass.mm"
include "sylib.mm"
include "ord.mm"
include "mpd.mm"
include "mpjaod.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "cdom.mm"
include "wbr.mm"
include "simpll.mm"
include "ccf.mm"
include "ad2antll.mm"
include "cpw.mm"
include "csdm.mm"
include "wral.mm"
include "elina.mm"
include "simp2bi.mm"
include "eqtrd.mm"
include "rankcf.mm"
include "fvex.mm"
include "domtri.mm"
include "mp2an.mm"
include "mpbir.mm"
include "syl6eqbrr.mm"
include "grudomon.mm"
include "syl112anc.mm"
include "cin.mm"
include "elin.mm"
include "biimpri.mm"
include "ordirr.mm"
include "adantl.mm"
include "pm2.21dd.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "pm2.18d.mm"
include "grur1a.mm"
include "eqssd.mm"

theorem grur1
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume gruina.1: |- A = ( U i^i On )


  assert |- ( ( U e. Univ /\ U e. U. ( R1 " On ) ) -> U = ( R1 ` A ) )

  proof
    cU
    cgru
    wcel
    #
    cU
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    wa
    #
    cU
    cA
    cr1
    cfv
    #
    @3
    cU
    @4
    wss
    #
    @3
    @5
    wn
    #
    vy
    cv
    #
    crnk
    cfv
    #
    cA
    wceq
    #
    vy
    cU
    wrex
    #
    @5
    @6
    vx
    cv
    #
    cU
    wcel
    #
    @11
    @4
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    @3
    @10
    vx
    cU
    @4
    nss
    @3
    @15
    @10
    vx
    @3
    @15
    @10
    @3
    @15
    wa
    #
    @11
    crnk
    cfv
    #
    cA
    wceq
    #
    @10
    cA
    @17
    wcel
    #
    @12
    @18
    @10
    wi
    @3
    @14
    @12
    @18
    @10
    @9
    @18
    vy
    @11
    cU
    @7
    @11
    wceq
    @8
    @17
    cA
    @7
    @11
    crnk
    fveq2
    eqeq1d
    rspcev
    ex
    ad2antrl
    @16
    @19
    cA
    crnk
    @11
    ctc
    cfv
    #
    cima
    #
    wcel
    #
    @10
    @16
    @17
    @21
    cA
    @16
    @11
    @1
    wcel
    #
    @17
    @21
    wceq
    @16
    @2
    @12
    @23
    @0
    @2
    @15
    simplr
    @3
    @12
    @14
    simprl
    @2
    cU
    @1
    @11
    cU
    r1elssi
    sseld
    sylc
    #
    @11
    tcrank
    syl
    eleq2d
    @0
    @12
    @22
    @10
    wi
    @2
    @14
    @0
    @12
    wa
    #
    @20
    cU
    wss
    #
    @22
    @9
    vy
    @20
    wrex
    #
    @10
    @25
    @11
    cU
    wss
    #
    cU
    wtr
    #
    @26
    @11
    cU
    gruelss
    @0
    @29
    @12
    cU
    grutr
    adantr
    @11
    cvv
    wcel
    @28
    @29
    wa
    @26
    wi
    vx
    vex
    @11
    cU
    cvv
    tcmin
    ax-mp
    syl2anc
    crnk
    wfun
    #
    @22
    @27
    @1
    con0
    crnk
    wf
    @30
    rankf
    @1
    con0
    crnk
    ffun
    ax-mp
    vy
    cA
    @20
    crnk
    fvelima
    mpan
    @9
    vy
    @20
    cU
    ssrexv
    syl2im
    ad2ant2r
    sylbid
    @16
    @17
    cA
    wcel
    #
    wn
    #
    @18
    @19
    wo
    #
    @16
    @13
    @31
    @3
    @12
    @14
    simprr
    @16
    @23
    cA
    cr1
    cdm
    #
    wcel
    #
    @13
    @31
    wb
    @24
    @0
    @12
    @35
    @2
    @14
    @25
    cA
    con0
    @34
    @25
    cA
    cina
    wcel
    #
    cA
    cwina
    wcel
    #
    cA
    con0
    wcel
    #
    @12
    @0
    cU
    c0
    wne
    #
    @36
    cU
    @11
    ne0i
    cA
    cU
    gruina.1
    gruina
    #
    sylan2
    cA
    inawina
    #
    cA
    winaon
    #
    3syl
    #
    cr1
    con0
    wfn
    @34
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    syl6eleqr
    ad2ant2r
    @11
    cA
    rankr1ag
    syl2anc
    mtbid
    @0
    @12
    @32
    @33
    wi
    @2
    @14
    @25
    @31
    @33
    @25
    @31
    @18
    @19
    w3o
    #
    @31
    @33
    wo
    @25
    @17
    con0
    wcel
    #
    @38
    @44
    @11
    rankon
    @43
    @45
    @17
    word
    cA
    word
    #
    @44
    @38
    @17
    eloni
    cA
    eloni
    #
    @17
    cA
    ordtri3or
    syl2an
    sylancr
    @31
    @18
    @19
    3orass
    sylib
    ord
    ad2ant2r
    mpd
    mpjaod
    ex
    exlimdv
    syl5bi
    @3
    @9
    @5
    vy
    cU
    @3
    @7
    cU
    wcel
    #
    @9
    wa
    #
    wa
    #
    cA
    cU
    wcel
    #
    @38
    @5
    @50
    @0
    @38
    @48
    cA
    @7
    cdom
    wbr
    @51
    @0
    @2
    @49
    simpll
    @50
    @36
    @37
    @38
    @0
    @48
    @36
    @2
    @9
    @48
    @0
    @39
    @36
    cU
    @7
    ne0i
    @40
    sylan2
    ad2ant2r
    #
    @41
    @42
    3syl
    #
    @3
    @48
    @9
    simprl
    @50
    cA
    @8
    ccf
    cfv
    #
    @7
    cdom
    @50
    @54
    cA
    ccf
    cfv
    #
    cA
    @9
    @54
    @55
    wceq
    @3
    @48
    @8
    cA
    ccf
    fveq2
    ad2antll
    @50
    @36
    @55
    cA
    wceq
    #
    @52
    @36
    cA
    c0
    wne
    @56
    @11
    cpw
    cA
    csdm
    wbr
    vx
    cA
    wral
    vx
    cA
    elina
    simp2bi
    syl
    eqtrd
    @54
    @7
    cdom
    wbr
    #
    @7
    @54
    csdm
    wbr
    wn
    #
    @7
    rankcf
    @54
    cvv
    wcel
    @7
    cvv
    wcel
    @57
    @58
    wb
    @8
    ccf
    fvex
    vy
    vex
    @54
    @7
    cvv
    cvv
    domtri
    mp2an
    mpbir
    syl6eqbrr
    cA
    @7
    cU
    grudomon
    syl112anc
    @53
    @51
    @38
    wa
    #
    cA
    cA
    wcel
    #
    @5
    @59
    cA
    cU
    con0
    cin
    #
    cA
    cA
    @61
    wcel
    @59
    cA
    cU
    con0
    elin
    biimpri
    gruina.1
    syl6eleqr
    @38
    @60
    wn
    #
    @51
    @38
    @46
    @62
    @47
    cA
    ordirr
    syl
    adantl
    pm2.21dd
    syl2anc
    rexlimdvaa
    syld
    pm2.18d
    @0
    @4
    cU
    wss
    @2
    cA
    cU
    gruina.1
    grur1a
    adantr
    eqssd
end
