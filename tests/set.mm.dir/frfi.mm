include "cfn.mm"
include "wcel.mm"
include "wpo.mm"
include "wfr.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "poeq2.mm"
include "freq2.mm"
include "imbi12d.mm"
include "weq.mm"
include "fr0.mm"
include "a1i.mm"
include "wss.mm"
include "ssun1.mm"
include "poss.mm"
include "ax-mp.mm"
include "imim1i.mm"
include "wa.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wal.mm"
include "cdif.mm"
include "uncom.mm"
include "sseq2i.mm"
include "ssundif.mm"
include "bitri.mm"
include "anbi1i.mm"
include "wel.mm"
include "breq1.mm"
include "cbvrexv.mm"
include "w3a.mm"
include "simpllr.mm"
include "simplrl.mm"
include "impcom.mm"
include "sylan2br.mm"
include "ad2ant2r.mm"
include "simpr1.mm"
include "simpr2.mm"
include "poirr.mm"
include "3ad2antr3.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "sylan.mm"
include "ne0i.mm"
include "syl.mm"
include "difss.mm"
include "cvv.mm"
include "vex.mm"
include "difexg.mm"
include "fri.mm"
include "mpanl1.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "syl12anc.mm"
include "notbid.mm"
include "rspcv.mm"
include "adantr.mm"
include "simplr2.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr3.mm"
include "simpr.mm"
include "potr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "con3d.mm"
include "ralsn.mm"
include "syl6ibr.mm"
include "syld.mm"
include "ralun.mm"
include "ex.mm"
include "sylcom.mm"
include "wb.mm"
include "difsnid.mm"
include "raleqdv.mm"
include "sylibd.mm"
include "reximdva.mm"
include "mpd.mm"
include "3exp2.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "ralnex.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "expcom.mm"
include "sylbir.mm"
include "pm2.61d1.mm"
include "difsn.mm"
include "expr.mm"
include "neeq1.mm"
include "raleq.mm"
include "rexbidv.mm"
include "syl5ibcom.mm"
include "com23.mm"
include "adantll.mm"
include "impr.mm"
include "syl5.mm"
include "pm2.61d.mm"
include "alrimiv.mm"
include "df-fr.mm"
include "sylibr.mm"
include "findcard2.mm"

theorem frfi
  let cA: class A
  let cR: class R
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R Po A /\ A e. Fin ) -> R Fr A )

  proof
    cA
    cfn
    wcel
    cA
    cR
    wpo
    #
    cA
    cR
    wfr
    #
    vx
    cv
    #
    cR
    wpo
    #
    @2
    cR
    wfr
    #
    wi
    c0
    cR
    wpo
    #
    c0
    cR
    wfr
    #
    wi
    vy
    cv
    #
    cR
    wpo
    #
    @7
    cR
    wfr
    #
    wi
    #
    @7
    vw
    cv
    #
    csn
    #
    cun
    #
    cR
    wpo
    #
    @13
    cR
    wfr
    #
    wi
    #
    @0
    @1
    wi
    vx
    vy
    vw
    cA
    @2
    c0
    wceq
    @3
    @5
    @4
    @6
    @2
    c0
    cR
    poeq2
    @2
    c0
    cR
    freq2
    imbi12d
    vx
    vy
    weq
    @3
    @8
    @4
    @9
    @2
    @7
    cR
    poeq2
    @2
    @7
    cR
    freq2
    imbi12d
    @2
    @13
    wceq
    @3
    @14
    @4
    @15
    @2
    @13
    cR
    poeq2
    @2
    @13
    cR
    freq2
    imbi12d
    @2
    cA
    wceq
    @3
    @0
    @4
    @1
    @2
    cA
    cR
    poeq2
    @2
    cA
    cR
    freq2
    imbi12d
    @6
    @5
    cR
    fr0
    a1i
    @10
    @16
    wi
    @7
    cfn
    wcel
    @10
    @14
    @9
    @15
    @14
    @8
    @9
    @7
    @13
    wss
    @14
    @8
    wi
    @7
    @12
    ssun1
    @7
    @13
    cR
    poss
    ax-mp
    imim1i
    @14
    @9
    @15
    @14
    @9
    wa
    #
    @2
    @13
    wss
    #
    @2
    c0
    wne
    #
    wa
    #
    vv
    cv
    #
    vu
    cv
    #
    cR
    wbr
    #
    wn
    #
    vv
    @2
    wral
    #
    vu
    @2
    wrex
    #
    wi
    #
    vx
    wal
    @15
    @17
    @27
    vx
    @20
    @2
    @12
    cdif
    #
    @7
    wss
    #
    @19
    wa
    #
    @17
    @26
    @18
    @29
    @19
    @18
    @2
    @12
    @7
    cun
    #
    wss
    @29
    @13
    @31
    @2
    @7
    @12
    uncom
    sseq2i
    @2
    @12
    @7
    ssundif
    bitri
    #
    anbi1i
    @17
    @30
    @26
    @17
    @30
    wa
    #
    vw
    vx
    wel
    #
    @26
    @33
    @21
    @11
    cR
    wbr
    #
    vv
    @2
    wrex
    #
    @34
    @26
    wi
    #
    @36
    vz
    cv
    #
    @11
    cR
    wbr
    #
    vz
    @2
    wrex
    @33
    @37
    @35
    @39
    vv
    vz
    @2
    @21
    @38
    @11
    cR
    breq1
    cbvrexv
    @33
    @39
    @37
    vz
    @2
    @33
    vz
    vx
    wel
    #
    @39
    @34
    @26
    @33
    @40
    @39
    @34
    w3a
    #
    wa
    #
    @24
    vv
    @28
    wral
    #
    vu
    @2
    wrex
    #
    @26
    @42
    @9
    @29
    @28
    c0
    wne
    #
    @44
    @14
    @9
    @30
    @41
    simpllr
    @17
    @29
    @19
    @41
    simplrl
    @42
    @38
    @28
    wcel
    #
    @45
    @33
    @3
    @41
    @46
    @14
    @29
    @3
    @9
    @19
    @29
    @14
    @18
    @3
    @32
    @18
    @14
    @3
    @2
    @13
    cR
    poss
    impcom
    sylan2br
    ad2ant2r
    #
    @3
    @41
    wa
    #
    @40
    @38
    @11
    wne
    #
    @46
    @3
    @40
    @39
    @34
    simpr1
    @48
    @39
    @11
    @11
    cR
    wbr
    wn
    #
    @49
    @3
    @40
    @39
    @34
    simpr2
    @3
    @40
    @34
    @50
    @39
    @2
    @11
    cR
    poirr
    3ad2antr3
    @38
    @11
    @11
    cR
    nbrne2
    syl2anc
    @38
    @2
    @11
    eldifsn
    sylanbrc
    #
    sylan
    @28
    @38
    ne0i
    syl
    @28
    @2
    wss
    @9
    @29
    @45
    wa
    #
    wa
    @43
    vu
    @28
    wrex
    #
    @44
    @2
    @12
    difss
    @28
    cvv
    wcel
    #
    @9
    @52
    @53
    @2
    cvv
    wcel
    @54
    vx
    vex
    @2
    @12
    cvv
    difexg
    ax-mp
    vu
    vv
    @7
    @28
    cvv
    cR
    fri
    mpanl1
    @43
    vu
    @28
    @2
    ssrexv
    mpsyl
    #
    syl12anc
    @33
    @3
    @41
    @44
    @26
    wi
    @47
    @48
    @43
    @25
    vu
    @2
    @48
    vu
    vx
    wel
    #
    wa
    #
    @43
    @24
    vv
    @28
    @12
    cun
    #
    wral
    #
    @25
    @57
    @43
    @24
    vv
    @12
    wral
    #
    @59
    @57
    @43
    @38
    @22
    cR
    wbr
    #
    wn
    #
    @60
    @48
    @43
    @62
    wi
    #
    @56
    @48
    @46
    @63
    @51
    @24
    @62
    vv
    @38
    @28
    vv
    vz
    weq
    @23
    @61
    @21
    @38
    @22
    cR
    breq1
    notbid
    rspcv
    syl
    adantr
    @57
    @62
    @11
    @22
    cR
    wbr
    #
    wn
    #
    @60
    @57
    @64
    @61
    @57
    @39
    @64
    @61
    @40
    @39
    @34
    @3
    @56
    simplr2
    @57
    @3
    @40
    @34
    @56
    @39
    @64
    wa
    @61
    wi
    @3
    @41
    @56
    simpll
    @40
    @39
    @34
    @3
    @56
    simplr1
    @40
    @39
    @34
    @3
    @56
    simplr3
    #
    @48
    @56
    simpr
    @2
    @38
    @11
    @22
    cR
    potr
    syl13anc
    mpand
    con3d
    @24
    @65
    vv
    @11
    vw
    vex
    vv
    vw
    weq
    @23
    @64
    @21
    @11
    @22
    cR
    breq1
    notbid
    ralsn
    syl6ibr
    syld
    @43
    @60
    @59
    @24
    vv
    @28
    @12
    ralun
    ex
    sylcom
    @57
    @34
    @59
    @25
    wb
    @66
    @34
    @24
    vv
    @58
    @2
    @2
    @11
    difsnid
    raleqdv
    syl
    sylibd
    reximdva
    sylan
    mpd
    3exp2
    rexlimdv
    syl5bi
    @36
    wn
    @35
    wn
    #
    vv
    @2
    wral
    #
    @37
    @35
    vv
    @2
    ralnex
    @34
    @68
    @26
    @25
    @68
    vu
    @11
    @2
    vu
    vw
    weq
    #
    @24
    @67
    vv
    @2
    @69
    @23
    @35
    @22
    @11
    @21
    cR
    breq2
    notbid
    ralbidv
    rspcev
    expcom
    sylbir
    pm2.61d1
    @34
    wn
    @28
    @2
    wceq
    #
    @33
    @26
    @11
    @2
    difsn
    @17
    @29
    @19
    @70
    @26
    wi
    #
    @9
    @29
    @19
    @71
    wi
    @14
    @9
    @29
    wa
    #
    @70
    @19
    @26
    @72
    @45
    @44
    wi
    @70
    @19
    @26
    wi
    @9
    @29
    @45
    @44
    @55
    expr
    @70
    @45
    @19
    @44
    @26
    @28
    @2
    c0
    neeq1
    @70
    @43
    @25
    vu
    @2
    @24
    vv
    @28
    @2
    raleq
    rexbidv
    imbi12d
    syl5ibcom
    com23
    adantll
    impr
    syl5
    pm2.61d
    ex
    syl5bi
    alrimiv
    vx
    vu
    vv
    @13
    cR
    df-fr
    sylibr
    ex
    sylcom
    a1i
    findcard2
    impcom
end
