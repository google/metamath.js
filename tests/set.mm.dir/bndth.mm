include "crn.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cioo.mm"
include "cmnf.mm"
include "csn.mm"
include "cxp.mm"
include "cima.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ctg.mm"
include "ctopon.mm"
include "retopon.mm"
include "eqeltri.mm"
include "toponunii.mm"
include "cnf.mm"
include "syl.mm"
include "frn.mm"
include "wi.mm"
include "imassrn.mm"
include "ctb.mm"
include "retopbas.mm"
include "bastg.mm"
include "ax-mp.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "ctop.mm"
include "retop.mm"
include "elexi.mm"
include "elpw2.mm"
include "mpbir.mm"
include "crest.mm"
include "ccmp.mm"
include "rncmp.mm"
include "syl2anc.mm"
include "wb.mm"
include "cmpsub.mm"
include "sylancr.mm"
include "mpbid.mm"
include "wceq.mm"
include "unieq.mm"
include "unissi.mm"
include "unirnioo.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "id.mm"
include "ltp1.mm"
include "cxr.mm"
include "wa.mm"
include "ressxr.mm"
include "peano2re.mm"
include "sseldi.mm"
include "elioomnf.mm"
include "mpbir2and.mm"
include "cop.mm"
include "df-ov.mm"
include "mnfxr.mm"
include "snid.mm"
include "opelxpi.mm"
include "wfun.mm"
include "cdm.mm"
include "ioof.mm"
include "ffun.mm"
include "snssi.mm"
include "xpss12.mm"
include "mp2an.mm"
include "fdmi.mm"
include "funfvima2.mm"
include "syl5eqel.mm"
include "elunii.mm"
include "ssriv.mm"
include "eqssi.mm"
include "syl6eq.mm"
include "sseq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "mpd.mm"
include "csup.mm"
include "simpr.mm"
include "elin.mm"
include "sylib.mm"
include "adantrr.mm"
include "simprd.mm"
include "simpld.mm"
include "elpwid.mm"
include "c0.mm"
include "wne.mm"
include "sseli.mm"
include "adantr.mm"
include "adantl.mm"
include "wn.mm"
include "mnflt.mm"
include "xrltnle.mm"
include "elsni.mm"
include "breq2d.mm"
include "mtbird.mm"
include "ioo0.mm"
include "syl2an.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "df-ioo.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxub.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "rgen2.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "supeq1d.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "wfn.mm"
include "ffn.mm"
include "supeq1.mm"
include "ralima.mm"
include "ssralv.mm"
include "mpisyl.mm"
include "fimaxre3.mm"
include "simplrr.mm"
include "sselda.mm"
include "eluni2.mm"
include "r19.29r.mm"
include "w3a.mm"
include "sspwuni.mm"
include "3ad2ant1.mm"
include "simp2r.mm"
include "sseldd.mm"
include "simp3l.mm"
include "r19.21bi.mm"
include "adantrl.mm"
include "3adant3.mm"
include "simp2l.mm"
include "syl6ss.mm"
include "supxrub.mm"
include "simp3r.mm"
include "letrd.mm"
include "3expia.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "adantlrr.mm"
include "syl5.mm"
include "expdimp.mm"
include "sylan2b.mm"
include "syldan.mm"
include "ralrimdva.mm"
include "ad2antrr.mm"
include "breq1.mm"
include "ralrn.mm"
include "sylibd.mm"
include "reximdva.mm"
include "rexlimddv.mm"

theorem bndth
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vw: setvar w
  assume bndth.1: |- X = U. J
  assume bndth.2: |- K = ( topGen ` ran (,) )
  assume bndth.3: |- ( ph -> J e. Comp )
  assume bndth.4: |- ( ph -> F e. ( J Cn K ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint J x
  disjoint J y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint K u
  disjoint K v
  disjoint K z
  disjoint u w
  disjoint ph u
  disjoint v w
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint X v
  disjoint X z
  disjoint J z
  assert |- ( ph -> E. x e. RR A. y e. X ( F ` y ) <_ x )

  proof
    wph
    cF
    crn
    #
    vv
    cv
    #
    cuni
    #
    wss
    #
    vy
    cv
    cF
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cr
    wrex
    #
    vv
    cioo
    cmnf
    csn
    #
    cr
    cxp
    #
    cima
    #
    cpw
    #
    cfn
    cin
    #
    wph
    @0
    cr
    wss
    #
    @3
    vv
    @13
    wrex
    #
    wph
    cX
    cr
    cF
    wf
    #
    @14
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @16
    bndth.4
    cF
    cJ
    cK
    cX
    cr
    bndth.1
    cr
    cK
    cK
    cioo
    crn
    #
    ctg
    cfv
    #
    cr
    ctopon
    cfv
    bndth.2
    retopon
    eqeltri
    toponunii
    #
    cnf
    syl
    #
    cX
    cr
    cF
    frn
    syl
    #
    @11
    cK
    cpw
    #
    wcel
    #
    wph
    @0
    vu
    cv
    #
    cuni
    #
    wss
    #
    @3
    vv
    @25
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vu
    @23
    wral
    #
    @14
    @15
    wi
    #
    @24
    @11
    cK
    wss
    @11
    @18
    cK
    cioo
    @10
    imassrn
    #
    @18
    @19
    cK
    @18
    ctb
    wcel
    @18
    @19
    wss
    retopbas
    @18
    ctb
    bastg
    ax-mp
    bndth.2
    sseqtr4i
    sstri
    @11
    cK
    cK
    ctop
    cK
    @19
    ctop
    bndth.2
    retop
    eqeltri
    #
    elexi
    elpw2
    mpbir
    wph
    cK
    @0
    crest
    co
    ccmp
    wcel
    #
    @32
    wph
    cJ
    ccmp
    wcel
    @17
    @36
    bndth.3
    bndth.4
    cF
    cJ
    cK
    rncmp
    syl2anc
    wph
    cK
    ctop
    wcel
    @14
    @36
    @32
    wb
    @35
    @22
    @0
    cK
    cr
    vu
    vv
    @20
    cmpsub
    sylancr
    mpbid
    @31
    @33
    vu
    @11
    @23
    @25
    @11
    wceq
    #
    @27
    @14
    @30
    @15
    @37
    @26
    cr
    @0
    @37
    @26
    @11
    cuni
    #
    cr
    @25
    @11
    unieq
    @38
    cr
    @38
    @18
    cuni
    cr
    @11
    @18
    @34
    unissi
    unirnioo
    sseqtr4i
    #
    vx
    cr
    @38
    @5
    cr
    wcel
    #
    @5
    cmnf
    @5
    c1
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    @42
    @11
    wcel
    @5
    @38
    wcel
    @40
    @43
    @40
    @5
    @41
    clt
    wbr
    #
    @40
    id
    @5
    ltp1
    @40
    @41
    cxr
    wcel
    @43
    @40
    @44
    wa
    wb
    @40
    cr
    cxr
    @41
    ressxr
    @5
    peano2re
    #
    sseldi
    @41
    @5
    elioomnf
    syl
    mpbir2and
    @40
    @42
    cmnf
    @41
    cop
    #
    cioo
    cfv
    #
    @11
    cmnf
    @41
    cioo
    df-ov
    @40
    @46
    @10
    wcel
    #
    @47
    @11
    wcel
    #
    @40
    cmnf
    @9
    wcel
    @41
    cr
    wcel
    @48
    cmnf
    cmnf
    cxr
    mnfxr
    elexi
    snid
    @45
    cmnf
    @41
    @9
    cr
    opelxpi
    sylancr
    cioo
    wfun
    #
    @10
    cioo
    cdm
    #
    wss
    @48
    @49
    wi
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    #
    @50
    ioof
    @52
    @53
    cioo
    ffun
    ax-mp
    @10
    @52
    @51
    @9
    cxr
    wss
    #
    cr
    cxr
    wss
    @10
    @52
    wss
    #
    cmnf
    cxr
    wcel
    #
    @55
    mnfxr
    cmnf
    cxr
    snssi
    ax-mp
    #
    ressxr
    @9
    cxr
    cr
    cxr
    xpss12
    mp2an
    #
    @52
    @53
    cioo
    ioof
    fdmi
    sseqtr4i
    @10
    @46
    cioo
    funfvima2
    mp2an
    syl
    syl5eqel
    @5
    @42
    @11
    elunii
    syl2anc
    ssriv
    eqssi
    syl6eq
    sseq2d
    @37
    @3
    vv
    @29
    @13
    @37
    @28
    @12
    cfn
    @25
    @11
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcv
    mpsyl
    mpd
    wph
    @1
    @13
    wcel
    #
    @3
    wa
    #
    wa
    #
    vw
    cv
    #
    cxr
    clt
    csup
    #
    @5
    cle
    wbr
    #
    vw
    @1
    wral
    #
    vx
    cr
    wrex
    #
    @8
    @62
    @1
    cfn
    wcel
    #
    @64
    cr
    wcel
    #
    vw
    @1
    wral
    #
    @67
    @62
    @1
    @12
    wcel
    #
    @68
    wph
    @60
    @71
    @68
    wa
    #
    @3
    wph
    @60
    wa
    #
    @60
    @72
    wph
    @60
    simpr
    @1
    @12
    cfn
    elin
    sylib
    #
    adantrr
    simprd
    wph
    @60
    @70
    @3
    @73
    @1
    @11
    wss
    #
    @69
    vw
    @11
    wral
    #
    @70
    @73
    @1
    @11
    @73
    @71
    @68
    @74
    simpld
    elpwid
    #
    @76
    vz
    cv
    #
    cioo
    cfv
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vz
    @10
    wral
    #
    @82
    @25
    @63
    cioo
    co
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vw
    cr
    wral
    vu
    @9
    wral
    @85
    vu
    vw
    @9
    cr
    @25
    @9
    wcel
    #
    @63
    cr
    wcel
    #
    wa
    #
    @84
    @63
    cr
    @88
    @25
    cxr
    wcel
    #
    @63
    cxr
    wcel
    #
    @83
    c0
    wne
    #
    @84
    @63
    wceq
    @86
    @89
    @87
    @9
    cxr
    @25
    @58
    sseli
    #
    adantr
    @87
    @90
    @86
    cr
    cxr
    @63
    ressxr
    sseli
    #
    adantl
    @88
    @91
    @63
    @25
    cle
    wbr
    #
    wn
    @88
    @94
    @63
    cmnf
    cle
    wbr
    #
    @87
    @95
    wn
    #
    @86
    @87
    cmnf
    @63
    clt
    wbr
    #
    @96
    @63
    mnflt
    @87
    @57
    @90
    @97
    @96
    wb
    mnfxr
    @93
    cmnf
    @63
    xrltnle
    sylancr
    mpbid
    adantl
    @88
    @25
    cmnf
    @63
    cle
    @86
    @25
    cmnf
    wceq
    @87
    @25
    cmnf
    elsni
    adantr
    breq2d
    mtbird
    @88
    @94
    @83
    c0
    @86
    @89
    @90
    @83
    c0
    wceq
    @94
    wb
    @87
    @92
    @93
    @25
    @63
    ioo0
    syl2an
    necon3abid
    mpbird
    vy
    vz
    vv
    vx
    @25
    @63
    clt
    clt
    cioo
    vy
    vz
    vv
    df-ioo
    @5
    cxr
    wcel
    #
    @90
    wa
    @5
    @63
    clt
    wbr
    idd
    @5
    @63
    xrltle
    @89
    @98
    wa
    @25
    @5
    clt
    wbr
    idd
    @25
    @5
    xrltle
    ixxub
    syl3anc
    @86
    @87
    simpr
    eqeltrd
    rgen2
    @81
    @85
    vz
    vu
    vw
    @9
    cr
    @78
    @25
    @63
    cop
    #
    wceq
    #
    @80
    @84
    cr
    @100
    cxr
    @79
    @83
    clt
    @100
    @79
    @99
    cioo
    cfv
    @83
    @78
    @99
    cioo
    fveq2
    @25
    @63
    cioo
    df-ov
    syl6eqr
    supeq1d
    eleq1d
    ralxp
    mpbir
    cioo
    @52
    wfn
    #
    @56
    @76
    @82
    wb
    @54
    @101
    ioof
    @52
    @53
    cioo
    ffn
    ax-mp
    @59
    @69
    @81
    vw
    vz
    @52
    @10
    cioo
    @63
    @79
    wceq
    @64
    @80
    cr
    cxr
    @63
    @79
    clt
    supeq1
    eleq1d
    ralima
    mp2an
    mpbir
    @69
    vw
    @1
    @11
    ssralv
    mpisyl
    #
    adantrr
    vx
    vw
    @1
    @64
    fimaxre3
    syl2anc
    @62
    @66
    @7
    vx
    cr
    @62
    @40
    wa
    #
    @66
    @78
    @5
    cle
    wbr
    #
    vz
    @0
    wral
    #
    @7
    @103
    @66
    @104
    vz
    @0
    @103
    @78
    @0
    wcel
    @78
    @2
    wcel
    #
    @66
    @104
    wi
    #
    @103
    @0
    @2
    @78
    wph
    @60
    @3
    @40
    simplrr
    sselda
    @106
    @103
    @78
    @63
    wcel
    #
    vw
    @1
    wrex
    #
    @107
    vw
    @78
    @1
    eluni2
    @103
    @109
    @66
    @104
    @109
    @66
    wa
    @108
    @65
    wa
    #
    vw
    @1
    wrex
    #
    @103
    @104
    @108
    @65
    vw
    @1
    r19.29r
    wph
    @60
    @40
    @111
    @104
    wi
    @3
    @73
    @40
    wa
    @110
    @104
    vw
    @1
    @73
    @40
    @63
    @1
    wcel
    #
    @110
    @104
    wi
    @73
    @40
    @112
    wa
    #
    @110
    @104
    @73
    @113
    @110
    w3a
    #
    @78
    @64
    @5
    @114
    @63
    cr
    @78
    @114
    @63
    cr
    @114
    @11
    @53
    @63
    @11
    @53
    wss
    @38
    cr
    wss
    @39
    @11
    cr
    sspwuni
    mpbir
    @114
    @1
    @11
    @63
    @73
    @113
    @75
    @110
    @77
    3ad2ant1
    @73
    @40
    @112
    @110
    simp2r
    sseldd
    sseldi
    elpwid
    #
    @73
    @113
    @108
    @65
    simp3l
    #
    sseldd
    @73
    @113
    @69
    @110
    @73
    @112
    @69
    @40
    @73
    @69
    vw
    @1
    @102
    r19.21bi
    adantrl
    3adant3
    @73
    @40
    @112
    @110
    simp2l
    @114
    @63
    cxr
    wss
    @108
    @78
    @64
    cle
    wbr
    @114
    @63
    cr
    cxr
    @115
    ressxr
    syl6ss
    @116
    @63
    @78
    supxrub
    syl2anc
    @73
    @113
    @108
    @65
    simp3r
    letrd
    3expia
    anassrs
    rexlimdva
    adantlrr
    syl5
    expdimp
    sylan2b
    syldan
    ralrimdva
    @103
    cF
    cX
    wfn
    #
    @105
    @7
    wb
    wph
    @117
    @61
    @40
    wph
    @16
    @117
    @21
    cX
    cr
    cF
    ffn
    syl
    ad2antrr
    @104
    @6
    vz
    vy
    cX
    cF
    @78
    @4
    @5
    cle
    breq1
    ralrn
    syl
    sylibd
    reximdva
    mpd
    rexlimddv
end
