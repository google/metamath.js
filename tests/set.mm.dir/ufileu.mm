include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cufil.mm"
include "cv.mm"
include "wss.mm"
include "wreu.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "ufilfil.mm"
include "wa.mm"
include "ufilmax.mm"
include "3expa.mm"
include "eqcomd.mm"
include "ex.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "ssid.mm"
include "sseq2.mm"
include "eqreu.mm"
include "mp3an2.mm"
include "mpdan.mm"
include "wb.mm"
include "wrex.mm"
include "reu6.mm"
include "ibibr.mm"
include "pm5.74ri.mm"
include "bitr3d.mm"
include "rspcva.mm"
include "adantll.mm"
include "filelss.mm"
include "syl.mm"
include "ad2antlr.mm"
include "wn.mm"
include "cdif.mm"
include "csn.mm"
include "cun.mm"
include "cfi.mm"
include "cfg.mm"
include "co.mm"
include "cfbas.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "filsspw.mm"
include "ad2antrr.mm"
include "difss.mm"
include "cvv.mm"
include "filtop.mm"
include "difexg.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "snssd.mm"
include "unssd.mm"
include "ssun1.mm"
include "filn0.mm"
include "ssn0.mm"
include "sylancr.mm"
include "cin.mm"
include "ad2ant2rl.mm"
include "df-ss.mm"
include "sylib.mm"
include "sseq1d.mm"
include "filss.mm"
include "3exp2.mm"
include "com23.mm"
include "impd.mm"
include "adantr.mm"
include "imp.mm"
include "sylbid.mm"
include "con3d.mm"
include "expr.mm"
include "impr.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "ralsng.mm"
include "inssdif0.mm"
include "necon3bbii.mm"
include "syl6bbr.mm"
include "mpbird.mm"
include "filfbas.mm"
include "difssd.mm"
include "ssdif0.mm"
include "eqss.mm"
include "simplbi2.mm"
include "eleq1.mm"
include "notbid.mm"
include "biimpcd.mm"
include "sylan9.mm"
include "adantl.mm"
include "syl5bir.mm"
include "necon2ad.mm"
include "mpd.mm"
include "snfbas.mm"
include "syl3anc.mm"
include "fbunfip.mm"
include "syl2anc.mm"
include "w3a.mm"
include "fsubbas.mm"
include "mpbir3and.mm"
include "fgcl.mm"
include "filssufil.mm"
include "r19.29.mm"
include "biimp.mm"
include "simpll.mm"
include "snex.mm"
include "unexg.mm"
include "sylancl.mm"
include "ssfii.mm"
include "ssfg.mm"
include "sstrd.mm"
include "unssad.mm"
include "sstr2.mm"
include "imim1d.mm"
include "a2i.mm"
include "syl56.mm"
include "rexlimdvw.mm"
include "syl5.mm"
include "mpan2d.mm"
include "an32s.mm"
include "snidg.mm"
include "elun2.mm"
include "sseldd.mm"
include "adantlr.mm"
include "simpllr.mm"
include "simprl.mm"
include "ufilb.mm"
include "con4d.mm"
include "mpdd.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "impbid2.mm"

theorem ufileu
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vg: setvar g
  let vx: setvar x

  disjoint F f
  disjoint X f
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint F g
  disjoint F x
  disjoint X g
  disjoint X x
  assert |- ( F e. ( Fil ` X ) -> ( F e. ( UFil ` X ) <-> E! f e. ( UFil ` X ) F C_ f ) )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cF
    cX
    cufil
    cfv
    #
    wcel
    #
    cF
    vf
    cv
    #
    wss
    #
    vf
    @2
    wreu
    #
    @3
    @5
    @4
    cF
    wceq
    #
    wi
    #
    vf
    @2
    wral
    #
    @6
    @3
    @8
    vf
    @2
    @4
    @2
    wcel
    @3
    @4
    @0
    wcel
    #
    @8
    @4
    cX
    ufilfil
    @3
    @10
    wa
    #
    @5
    @7
    @11
    @5
    wa
    cF
    @4
    @3
    @10
    @5
    cF
    @4
    wceq
    cF
    @4
    cX
    ufilmax
    3expa
    eqcomd
    ex
    sylan2
    ralrimiva
    @3
    cF
    cF
    wss
    #
    @9
    @6
    cF
    ssid
    @5
    @12
    vf
    @2
    cF
    @4
    cF
    cF
    sseq2
    eqreu
    mp3an2
    mpdan
    @6
    @5
    @4
    vg
    cv
    #
    wceq
    #
    wb
    #
    vf
    @2
    wral
    #
    vg
    @2
    wrex
    @1
    @3
    @5
    vf
    vg
    @2
    reu6
    @1
    @16
    @3
    vg
    @2
    @1
    @13
    @2
    wcel
    #
    wa
    #
    @16
    @3
    @18
    @16
    wa
    #
    cF
    @13
    @2
    @19
    cF
    @13
    @17
    @16
    cF
    @13
    wss
    #
    @1
    @15
    @20
    vf
    @13
    @2
    @14
    @5
    @15
    @20
    @14
    @5
    @15
    @14
    @5
    ibibr
    pm5.74ri
    @4
    @13
    cF
    sseq2
    bitr3d
    rspcva
    adantll
    @19
    vx
    @13
    cF
    @19
    vx
    cv
    #
    @13
    wcel
    #
    @21
    cX
    wss
    #
    @21
    cF
    wcel
    #
    @17
    @22
    @23
    wi
    #
    @1
    @16
    @17
    @13
    @0
    wcel
    #
    @25
    @13
    cX
    ufilfil
    @26
    @22
    @23
    @21
    @13
    cX
    filelss
    ex
    syl
    ad2antlr
    @19
    @23
    @22
    @24
    @19
    @23
    @22
    @24
    wi
    @19
    @23
    wa
    @24
    @22
    @19
    @23
    @24
    wn
    #
    @22
    wn
    #
    @19
    @23
    @27
    wa
    #
    wa
    #
    @28
    cX
    @21
    cdif
    #
    @13
    wcel
    #
    @30
    cX
    cF
    @31
    csn
    #
    cun
    #
    cfi
    cfv
    #
    cfg
    co
    #
    @13
    @31
    @18
    @29
    @16
    @36
    @13
    wss
    #
    @18
    @29
    wa
    #
    @16
    @37
    @38
    @16
    @36
    @4
    wss
    #
    vf
    @2
    wrex
    #
    @37
    @38
    @36
    @0
    wcel
    #
    @40
    @38
    @35
    cX
    cfbas
    cfv
    #
    wcel
    #
    @41
    @38
    @43
    @34
    cX
    cpw
    #
    wss
    #
    @34
    c0
    wne
    #
    c0
    @35
    wcel
    wn
    #
    @38
    cF
    @33
    @44
    @1
    cF
    @44
    wss
    @17
    @29
    cF
    cX
    filsspw
    ad2antrr
    @38
    @31
    @44
    @38
    @31
    @44
    wcel
    #
    @31
    cX
    wss
    #
    cX
    @21
    difss
    @38
    @31
    cvv
    wcel
    #
    @48
    @49
    wb
    @38
    cX
    cF
    wcel
    #
    @50
    @1
    @51
    @17
    @29
    cF
    cX
    filtop
    ad2antrr
    #
    cX
    @21
    cF
    difexg
    syl
    #
    @31
    cX
    cvv
    elpwg
    syl
    mpbiri
    snssd
    unssd
    @38
    cF
    @34
    wss
    cF
    c0
    wne
    #
    @46
    cF
    @33
    ssun1
    @1
    @54
    @17
    @29
    cF
    cX
    filn0
    ad2antrr
    cF
    @34
    ssn0
    sylancr
    @38
    @47
    @4
    @13
    cin
    #
    c0
    wne
    #
    vg
    @33
    wral
    #
    vf
    cF
    wral
    #
    @38
    @57
    vf
    cF
    @38
    @4
    cF
    wcel
    #
    wa
    @57
    @4
    cX
    cin
    #
    @21
    wss
    #
    wn
    #
    @38
    @59
    @62
    @18
    @23
    @27
    @59
    @62
    wi
    @18
    @23
    wa
    @59
    @27
    @62
    @18
    @23
    @59
    @27
    @62
    wi
    @18
    @23
    @59
    wa
    #
    wa
    #
    @61
    @24
    @64
    @61
    @4
    @21
    wss
    #
    @24
    @64
    @60
    @4
    @21
    @64
    @4
    cX
    wss
    #
    @60
    @4
    wceq
    @1
    @59
    @66
    @17
    @23
    @4
    cF
    cX
    filelss
    ad2ant2rl
    @4
    cX
    df-ss
    sylib
    sseq1d
    @18
    @63
    @65
    @24
    wi
    #
    @1
    @63
    @67
    wi
    @17
    @1
    @23
    @59
    @67
    @1
    @59
    @23
    @67
    @1
    @59
    @23
    @65
    @24
    @4
    @21
    cF
    cX
    filss
    3exp2
    com23
    impd
    adantr
    imp
    sylbid
    con3d
    expr
    com23
    impr
    imp
    @38
    @57
    @62
    wb
    #
    @59
    @38
    @50
    @68
    @53
    @50
    @57
    @4
    @31
    cin
    #
    c0
    wne
    #
    @62
    @56
    @70
    vg
    @31
    cvv
    @13
    @31
    wceq
    @55
    @69
    c0
    @13
    @31
    @4
    ineq2
    neeq1d
    ralsng
    @61
    @69
    c0
    @4
    cX
    @21
    inssdif0
    necon3bbii
    syl6bbr
    syl
    adantr
    mpbird
    ralrimiva
    @38
    cF
    @42
    wcel
    #
    @33
    @42
    wcel
    #
    @47
    @58
    wb
    @1
    @71
    @17
    @29
    cF
    cX
    filfbas
    ad2antrr
    @38
    @49
    @31
    c0
    wne
    #
    @51
    @72
    @38
    cX
    @21
    difssd
    @38
    @51
    @73
    @52
    @38
    @51
    @31
    c0
    @31
    c0
    wceq
    cX
    @21
    wss
    #
    @38
    @51
    wn
    #
    cX
    @21
    ssdif0
    @29
    @74
    @75
    wi
    @18
    @23
    @74
    @21
    cX
    wceq
    #
    @27
    @75
    @76
    @23
    @74
    @21
    cX
    eqss
    simplbi2
    @76
    @27
    @75
    @76
    @24
    @51
    @21
    cX
    cF
    eleq1
    notbid
    biimpcd
    sylan9
    adantl
    syl5bir
    necon2ad
    mpd
    @52
    @31
    cX
    cF
    snfbas
    syl3anc
    vf
    vg
    cF
    @33
    cX
    cX
    fbunfip
    syl2anc
    mpbird
    @38
    @51
    @43
    @45
    @46
    @47
    w3a
    wb
    @52
    @34
    cF
    cX
    fsubbas
    syl
    mpbir3and
    #
    @35
    cX
    fgcl
    syl
    vf
    @36
    cX
    filssufil
    syl
    @16
    @40
    wa
    @15
    @39
    wa
    #
    vf
    @2
    wrex
    @38
    @37
    @15
    @39
    vf
    @2
    r19.29
    @38
    @78
    @37
    vf
    @2
    @38
    @15
    @39
    @37
    @15
    @5
    @14
    wi
    @38
    @39
    @14
    wi
    @39
    @37
    wi
    @5
    @14
    biimp
    @38
    @39
    @5
    @14
    @38
    cF
    @36
    wss
    @39
    @5
    wi
    @38
    cF
    @33
    @36
    @38
    @34
    @35
    @36
    @38
    @34
    cvv
    wcel
    #
    @34
    @35
    wss
    @38
    @1
    @33
    cvv
    wcel
    @79
    @1
    @17
    @29
    simpll
    @31
    snex
    cF
    @33
    @0
    cvv
    unexg
    sylancl
    @34
    cvv
    ssfii
    syl
    @38
    @43
    @35
    @36
    wss
    @77
    @35
    cX
    ssfg
    syl
    sstrd
    #
    unssad
    cF
    @36
    @4
    sstr2
    syl
    imim1d
    @39
    @14
    @37
    @14
    @39
    @37
    @4
    @13
    @36
    sseq2
    biimpcd
    a2i
    syl56
    impd
    rexlimdvw
    syl5
    mpan2d
    imp
    an32s
    @18
    @29
    @31
    @36
    wcel
    @16
    @38
    @34
    @36
    @31
    @80
    @38
    @31
    @33
    wcel
    #
    @31
    @34
    wcel
    @38
    @50
    @81
    @53
    @31
    cvv
    snidg
    syl
    @31
    @33
    cF
    elun2
    syl
    sseldd
    adantlr
    sseldd
    @30
    @17
    @23
    @28
    @32
    wb
    @1
    @17
    @16
    @29
    simpllr
    @19
    @23
    @27
    simprl
    @21
    @13
    cX
    ufilb
    syl2anc
    mpbird
    expr
    con4d
    ex
    com23
    mpdd
    ssrdv
    eqssd
    @1
    @17
    @16
    simplr
    eqeltrd
    ex
    rexlimdva
    syl5bi
    impbid2
end
