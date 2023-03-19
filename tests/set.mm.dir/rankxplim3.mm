include "cxp.mm"
include "crnk.mm"
include "cfv.mm"
include "wlim.mm"
include "cuni.mm"
include "limuni2.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "cun.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "0ellim.mm"
include "n0i.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "con3i.mm"
include "3syl.mm"
include "wss.mm"
include "rankon.mm"
include "onsuci.mm"
include "elexi.mm"
include "sucid.mm"
include "wb.mm"
include "ontri1.mm"
include "mp2an.mm"
include "con2bii.mm"
include "mpbi.mm"
include "rankxpu.mm"
include "sstr.mm"
include "mpan2.mm"
include "mto.mm"
include "reeanv.mm"
include "wi.mm"
include "simprl.mm"
include "simpr.mm"
include "rankuni.mm"
include "unieqi.mm"
include "eqtri.mm"
include "wne.mm"
include "df-ne.mm"
include "xpex.mm"
include "rankeq0.mm"
include "notbii.mm"
include "bitr2i.mm"
include "sylib.mm"
include "unixp.mm"
include "syl.mm"
include "fveq2d.mm"
include "syl5reqr.mm"
include "eqimss.mm"
include "adantr.mm"
include "eqsstr3d.mm"
include "adantrr.mm"
include "limuni.mm"
include "sseqtr4d.mm"
include "cvv.mm"
include "word.mm"
include "vex.mm"
include "onordi.mm"
include "orduni.mm"
include "ax-mp.mm"
include "ordelsuc.mm"
include "sylibr.mm"
include "limsuc.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "ordsucelsuc.mm"
include "onsucuni2.mm"
include "mpan.mm"
include "ad2antll.mm"
include "eleqtrd.mm"
include "onsucssi.mm"
include "ex.mm"
include "a1d.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "mtoi.mm"
include "wo.mm"
include "ianor.mm"
include "un00.mm"
include "olc.mm"
include "adantl.mm"
include "sylbir.mm"
include "xpeq0.mm"
include "unex.mm"
include "w3o.mm"
include "ordzsl.mm"
include "3ori.mm"
include "sylan.mm"
include "orim12d.mm"
include "syl5bi.mm"
include "imp.mm"
include "simpl.mm"
include "necon3abii.mm"
include "rankxplim.mm"
include "sylan2br.mm"
include "limeq.mm"
include "mpbird.mm"
include "expcom.mm"
include "idd.mm"
include "jaod.mm"
include "mpd.mm"
include "syl2anc.mm"
include "impbii.mm"

theorem rankxplim3
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rankxplim.1: |- A e. _V
  assume rankxplim.2: |- B e. _V


  assert |- ( Lim ( rank ` ( A X. B ) ) <-> Lim U. ( rank ` ( A X. B ) ) )

  proof
    cA
    cB
    cxp
    #
    crnk
    cfv
    #
    wlim
    #
    @1
    cuni
    #
    wlim
    #
    @1
    limuni2
    @4
    @1
    c0
    wceq
    #
    wn
    #
    cA
    cB
    cun
    #
    crnk
    cfv
    #
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    @1
    vy
    cv
    #
    csuc
    wceq
    #
    vy
    con0
    wrex
    #
    wa
    #
    wn
    #
    @2
    @4
    c0
    @3
    wcel
    @3
    c0
    wceq
    #
    wn
    @6
    @3
    0ellim
    @3
    c0
    n0i
    @5
    @18
    @5
    @3
    c0
    cuni
    c0
    @1
    c0
    unieq
    uni0
    syl6eq
    con3i
    3syl
    #
    @4
    @16
    @8
    csuc
    #
    csuc
    #
    csuc
    #
    @1
    wss
    #
    @23
    @22
    @21
    wss
    #
    @21
    @22
    wcel
    #
    @24
    wn
    @21
    @21
    con0
    @20
    @8
    @7
    rankon
    #
    onsuci
    onsuci
    #
    elexi
    sucid
    @24
    @25
    @22
    con0
    wcel
    @21
    con0
    wcel
    @24
    @25
    wn
    wb
    @21
    @27
    onsuci
    @27
    @22
    @21
    ontri1
    mp2an
    con2bii
    mpbi
    @23
    @1
    @21
    wss
    @24
    cA
    cB
    rankxplim.1
    rankxplim.2
    rankxpu
    @22
    @1
    @21
    sstr
    mpan2
    mto
    @16
    @11
    @14
    wa
    #
    vy
    con0
    wrex
    vx
    con0
    wrex
    @4
    @23
    @11
    @14
    vx
    vy
    con0
    con0
    reeanv
    @4
    @28
    @23
    vx
    vy
    con0
    con0
    @4
    @28
    @23
    wi
    @9
    con0
    wcel
    @13
    con0
    wcel
    wa
    @4
    @28
    @23
    @4
    @28
    wa
    #
    @21
    @1
    wcel
    @23
    @29
    @21
    @3
    csuc
    #
    @1
    @29
    @20
    @3
    wcel
    #
    @21
    @30
    wcel
    #
    @29
    @8
    @3
    wcel
    #
    @31
    @29
    @8
    @10
    @3
    @4
    @11
    @14
    simprl
    @29
    @9
    @3
    wcel
    #
    @10
    @3
    wcel
    #
    @29
    @10
    @3
    wss
    #
    @34
    @29
    @10
    @3
    cuni
    #
    @3
    @4
    @11
    @10
    @37
    wss
    @14
    @4
    @11
    wa
    @10
    @8
    @37
    @4
    @11
    simpr
    @4
    @8
    @37
    wss
    #
    @11
    @4
    @8
    @37
    wceq
    @38
    @4
    @37
    @0
    cuni
    #
    cuni
    #
    crnk
    cfv
    #
    @8
    @41
    @39
    crnk
    cfv
    #
    cuni
    @37
    @39
    rankuni
    @42
    @3
    @0
    rankuni
    unieqi
    eqtri
    @4
    @40
    @7
    crnk
    @4
    @0
    c0
    wne
    #
    @40
    @7
    wceq
    @4
    @6
    @43
    @19
    @43
    @0
    c0
    wceq
    #
    wn
    #
    @6
    @0
    c0
    df-ne
    @44
    @5
    @0
    cA
    cB
    rankxplim.1
    rankxplim.2
    xpex
    rankeq0
    #
    notbii
    #
    bitr2i
    sylib
    cA
    cB
    unixp
    syl
    fveq2d
    syl5reqr
    @8
    @37
    eqimss
    syl
    adantr
    eqsstr3d
    adantrr
    @4
    @3
    @37
    wceq
    @28
    @3
    limuni
    adantr
    sseqtr4d
    @9
    cvv
    wcel
    @3
    word
    #
    @34
    @36
    wb
    vx
    vex
    @1
    word
    #
    @48
    @1
    @0
    rankon
    #
    onordi
    #
    @1
    orduni
    ax-mp
    #
    @9
    @3
    cvv
    ordelsuc
    mp2an
    sylibr
    @4
    @34
    @35
    wb
    @28
    @3
    @9
    limsuc
    adantr
    mpbid
    eqeltrd
    @4
    @33
    @31
    wb
    @28
    @3
    @8
    limsuc
    adantr
    mpbid
    @48
    @31
    @32
    wb
    @52
    @20
    @3
    ordsucelsuc
    ax-mp
    sylib
    @14
    @30
    @1
    wceq
    #
    @4
    @11
    @1
    con0
    wcel
    @14
    @53
    @50
    @1
    @13
    onsucuni2
    mpan
    ad2antll
    eleqtrd
    @21
    @1
    @27
    @50
    onsucssi
    sylib
    ex
    a1d
    rexlimdvv
    syl5bir
    mtoi
    @6
    @17
    wa
    @8
    wlim
    #
    @2
    wo
    #
    @2
    @6
    @17
    @55
    @17
    @12
    wn
    #
    @15
    wn
    #
    wo
    @6
    @55
    @12
    @15
    ianor
    @6
    @56
    @54
    @57
    @2
    @6
    @56
    @54
    @6
    @8
    c0
    wceq
    #
    wn
    #
    @56
    @54
    @6
    @7
    c0
    wceq
    #
    wn
    #
    @59
    @6
    @45
    @61
    @47
    @60
    @44
    @60
    cA
    c0
    wceq
    #
    cB
    c0
    wceq
    #
    wo
    #
    @44
    @60
    @62
    @63
    wa
    @64
    cA
    cB
    un00
    @63
    @64
    @62
    @63
    @62
    olc
    adantl
    sylbir
    cA
    cB
    xpeq0
    sylibr
    con3i
    sylbir
    @60
    @58
    @7
    cA
    cB
    rankxplim.1
    rankxplim.2
    unex
    rankeq0
    notbii
    sylib
    @58
    @12
    @54
    @8
    word
    @58
    @12
    @54
    w3o
    @8
    @26
    onordi
    vx
    @8
    ordzsl
    mpbi
    3ori
    sylan
    ex
    @6
    @57
    @2
    @5
    @15
    @2
    @49
    @5
    @15
    @2
    w3o
    @51
    vy
    @1
    ordzsl
    mpbi
    3ori
    ex
    orim12d
    syl5bi
    imp
    @6
    @55
    @2
    wi
    @17
    @6
    @54
    @2
    @2
    @54
    @6
    @2
    @54
    @6
    wa
    #
    @2
    @54
    @54
    @6
    simpl
    @65
    @1
    @8
    wceq
    #
    @2
    @54
    wb
    @6
    @54
    @43
    @66
    @5
    @0
    c0
    @46
    necon3abii
    cA
    cB
    rankxplim.1
    rankxplim.2
    rankxplim
    sylan2br
    @1
    @8
    limeq
    syl
    mpbird
    expcom
    @6
    @2
    idd
    jaod
    adantr
    mpd
    syl2anc
    impbii
end
