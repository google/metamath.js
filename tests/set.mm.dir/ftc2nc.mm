include "cfv.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "citg.mm"
include "cmin.mm"
include "caddc.mm"
include "cneg.mm"
include "cicc.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "wceq.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "fvex.mm"
include "fvconst2.mm"
include "syl.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "subcn.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "ioossre.mm"
include "cc.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "cabs.mm"
include "wel.mm"
include "cc0.mm"
include "cif.mm"
include "citg2.mm"
include "cima.mm"
include "wrex.mm"
include "wfun.mm"
include "cpw.mm"
include "ioof.mm"
include "ffun.mm"
include "ax-mp.mm"
include "fvelima.mm"
include "mpan.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "wb.mm"
include "cop.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "jca.mm"
include "adantr.mm"
include "xp1st.mm"
include "w3a.mm"
include "elicc1.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp2d.mm"
include "sylan2.mm"
include "xp2nd.mm"
include "iccleub.mm"
include "3expa.mm"
include "syl2an.mm"
include "ioossioo.mm"
include "syl12anc.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "syldan.mm"
include "cvv.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "fvexd.mm"
include "cibl.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "iblss.mm"
include "cmbf.mm"
include "ax-resscn.mm"
include "cncfss.mm"
include "mp2an.mm"
include "abscncf.mm"
include "sselii.mm"
include "cres.mm"
include "reseq1d.mm"
include "resmptd.mm"
include "eqtrd.mm"
include "rescncf.mm"
include "sylc.mm"
include "cncfmpt1f.mm"
include "cnmbf.mm"
include "sylancr.mm"
include "ccj.mm"
include "csb.mm"
include "cmul.mm"
include "itgcl.mm"
include "cjcld.mm"
include "sstri.mm"
include "cncfmptc.mm"
include "mp3an23.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "syl5eqelr.mm"
include "mulcncf.mm"
include "itgabsnc.mm"
include "abscld.mm"
include "iblabsnc.mm"
include "absge0d.mm"
include "itgposval.mm"
include "breqtrd.mm"
include "itgeq1.mm"
include "eleq2.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "breq12d.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "ftc1anc.mm"
include "cncfmpt2f.mm"
include "crn.mm"
include "ctg.mm"
include "iccssre.mm"
include "elicc2.mm"
include "simp3d.mm"
include "iooss2.mm"
include "subcld.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "ioossicc.mm"
include "sseli.mm"
include "ftc1cnnc.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "3eqtr3rd.mm"
include "dvmptsub.mm"
include "subidd.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"
include "fconstmpt.mm"
include "dveq0.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqtr3d.mm"
include "lbicc2.mm"
include "c0.mm"
include "iooid.mm"
include "syl6eq.mm"
include "itg0.mm"
include "df-neg.mm"
include "negex.mm"
include "ffvelrnd.mm"
include "pncan3d.mm"
include "negsubd.mm"

theorem ftc2nc
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cF: class F
  let vs: setvar s
  let vx: setvar x
  assume ftc2nc.a: |- ( ph -> A e. RR )
  assume ftc2nc.b: |- ( ph -> B e. RR )
  assume ftc2nc.le: |- ( ph -> A <_ B )
  assume ftc2nc.c: |- ( ph -> ( RR _D F ) e. ( ( A (,) B ) -cn-> CC ) )
  assume ftc2nc.i: |- ( ph -> ( RR _D F ) e. L^1 )
  assume ftc2nc.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> CC ) )

  disjoint A t
  disjoint B t
  disjoint F t
  disjoint ph t
  disjoint s t
  disjoint s x
  disjoint A s
  disjoint t x
  disjoint A x
  disjoint B s
  disjoint B x
  disjoint F s
  disjoint F x
  disjoint ph s
  disjoint ph x
  assert |- ( ph -> S. ( A (,) B ) ( ( RR _D F ) ` t ) _d t = ( ( F ` B ) - ( F ` A ) ) )

  proof
    wph
    cB
    cF
    cfv
    #
    vt
    cA
    cB
    cioo
    co
    #
    vt
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    citg
    #
    @0
    cmin
    co
    #
    caddc
    co
    @0
    cA
    cF
    cfv
    #
    cneg
    #
    caddc
    co
    @5
    @0
    @7
    cmin
    co
    wph
    @6
    @8
    @0
    caddc
    wph
    cB
    cA
    cB
    cicc
    co
    #
    cA
    vx
    @9
    vt
    cA
    vx
    cv
    #
    cioo
    co
    #
    @4
    citg
    #
    @10
    cF
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    csn
    cxp
    #
    cfv
    #
    @16
    @6
    @8
    wph
    cB
    @9
    wcel
    #
    @18
    @16
    wceq
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    @19
    wph
    cA
    ftc2nc.a
    rexrd
    #
    wph
    cB
    ftc2nc.b
    rexrd
    #
    ftc2nc.le
    cA
    cB
    ubicc2
    syl3anc
    #
    @9
    @16
    cB
    cA
    @15
    fvex
    fvconst2
    syl
    wph
    cB
    @15
    cfv
    #
    @18
    @6
    wph
    cB
    @15
    @17
    wph
    cA
    cB
    @15
    ftc2nc.a
    ftc2nc.b
    wph
    vx
    @12
    @13
    cmin
    ccnfld
    ctopn
    cfv
    #
    @9
    @27
    eqid
    #
    cmin
    @27
    @27
    ctx
    co
    @27
    ccn
    co
    wcel
    wph
    @27
    @28
    subcn
    a1i
    wph
    vx
    vt
    cA
    cB
    @1
    @3
    vx
    @9
    @12
    cmpt
    #
    vs
    @29
    eqid
    #
    ftc2nc.a
    ftc2nc.b
    ftc2nc.le
    @1
    @1
    wss
    wph
    @1
    ssid
    a1i
    @1
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    ftc2nc.i
    wph
    @3
    @1
    cc
    ccncf
    co
    wcel
    #
    @1
    cc
    @3
    wf
    ftc2nc.c
    @1
    cc
    @3
    cncff
    syl
    #
    wph
    vt
    vs
    cv
    #
    @4
    citg
    #
    cabs
    cfv
    #
    vt
    cr
    vt
    vs
    wel
    #
    @4
    cabs
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cle
    wbr
    #
    vs
    cioo
    @9
    @9
    cxp
    #
    cima
    #
    @33
    @43
    wcel
    #
    @10
    cioo
    cfv
    #
    @33
    wceq
    #
    vx
    @42
    wrex
    #
    wph
    @41
    cioo
    wfun
    #
    @44
    @47
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    @48
    ioof
    @49
    @50
    cioo
    ffun
    ax-mp
    vx
    @33
    @42
    cioo
    fvelima
    mpan
    wph
    @46
    @41
    vx
    @42
    wph
    @10
    @42
    wcel
    #
    wa
    #
    @46
    @10
    c1st
    cfv
    #
    @10
    c2nd
    cfv
    #
    cioo
    co
    #
    @33
    wceq
    #
    @41
    @51
    @46
    @56
    wb
    wph
    @51
    @45
    @55
    @33
    @51
    @45
    @53
    @54
    cop
    #
    cioo
    cfv
    @55
    @51
    @10
    @57
    cioo
    @10
    @9
    @9
    1st2nd2
    fveq2d
    @53
    @54
    cioo
    df-ov
    syl6eqr
    eqeq1d
    adantl
    @52
    vt
    @55
    @4
    citg
    #
    cabs
    cfv
    #
    vt
    cr
    @2
    @55
    wcel
    #
    @37
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cle
    wbr
    @56
    @41
    @52
    @59
    vt
    @55
    @37
    citg
    @63
    cle
    @52
    vt
    vs
    @55
    @4
    cc
    @52
    @60
    @2
    @1
    wcel
    #
    @4
    cc
    wcel
    #
    @52
    @55
    @1
    @2
    @52
    @20
    @21
    wa
    #
    cA
    @53
    cle
    wbr
    #
    @54
    cB
    cle
    wbr
    #
    @55
    @1
    wss
    #
    wph
    @66
    @51
    wph
    @20
    @21
    @23
    @24
    jca
    #
    adantr
    @51
    wph
    @53
    @9
    wcel
    #
    @67
    @10
    @9
    @9
    xp1st
    wph
    @71
    wa
    @53
    cxr
    wcel
    #
    @67
    @53
    cB
    cle
    wbr
    #
    wph
    @71
    @72
    @67
    @73
    w3a
    #
    wph
    @20
    @21
    @71
    @74
    wb
    @23
    @24
    cA
    cB
    @53
    elicc1
    syl2anc
    biimpa
    simp2d
    sylan2
    wph
    @66
    @54
    @9
    wcel
    #
    @68
    @51
    @70
    @10
    @9
    @9
    xp2nd
    @20
    @21
    @75
    @68
    cA
    cB
    @54
    iccleub
    3expa
    syl2an
    cA
    cB
    @53
    @54
    ioossioo
    syl12anc
    #
    sselda
    wph
    @64
    @65
    @51
    wph
    @1
    cc
    @2
    @3
    @32
    ffvelrnda
    adantlr
    syldan
    #
    @52
    vt
    @55
    @1
    @4
    cvv
    @76
    @55
    cvol
    cdm
    #
    wcel
    #
    @52
    @53
    @54
    ioombl
    #
    a1i
    @52
    @64
    wa
    @2
    @3
    fvexd
    wph
    vt
    @1
    @4
    cmpt
    #
    cibl
    wcel
    #
    @51
    wph
    @3
    @81
    cibl
    wph
    vt
    @1
    cc
    @3
    @32
    feqmptd
    #
    ftc2nc.i
    eqeltrrd
    #
    adantr
    iblss
    #
    @52
    @79
    vt
    @55
    @37
    cmpt
    #
    @55
    cc
    ccncf
    co
    #
    wcel
    @86
    cmbf
    wcel
    @80
    @52
    vt
    @4
    cabs
    @55
    cabs
    cc
    cc
    ccncf
    co
    #
    wcel
    @52
    cc
    cr
    ccncf
    co
    #
    @88
    cabs
    cr
    cc
    wss
    #
    cc
    cc
    wss
    #
    @89
    @88
    wss
    ax-resscn
    cc
    ssid
    #
    cc
    cr
    cc
    cncfss
    mp2an
    abscncf
    sselii
    a1i
    @52
    @3
    @55
    cres
    #
    vt
    @55
    @4
    cmpt
    #
    @87
    @52
    @93
    @81
    @55
    cres
    #
    @94
    wph
    @93
    @95
    wceq
    @51
    wph
    @3
    @81
    @55
    @83
    reseq1d
    adantr
    @52
    vt
    @1
    @55
    @4
    @76
    resmptd
    eqtrd
    @52
    @69
    @31
    @93
    @87
    wcel
    @76
    wph
    @31
    @51
    ftc2nc.c
    adantr
    @1
    cc
    @55
    @3
    rescncf
    sylc
    eqeltrrd
    #
    cncfmpt1f
    @55
    @86
    cnmbf
    sylancr
    #
    @52
    @79
    vs
    @55
    @58
    ccj
    cfv
    #
    vt
    @33
    @4
    csb
    #
    cmul
    co
    cmpt
    #
    @87
    wcel
    @100
    cmbf
    wcel
    @80
    @52
    vs
    @98
    @99
    @55
    @52
    @98
    cc
    wcel
    #
    vs
    @55
    @98
    cmpt
    @87
    wcel
    #
    @52
    @58
    @52
    vt
    @55
    @4
    cc
    @77
    @85
    itgcl
    cjcld
    @101
    @55
    cc
    wss
    @91
    @102
    @55
    cr
    cc
    @53
    @54
    ioossre
    ax-resscn
    sstri
    @92
    vs
    @98
    @55
    cc
    cncfmptc
    mp3an23
    syl
    @52
    vs
    @55
    @99
    cmpt
    @94
    @87
    vt
    vs
    @55
    @4
    @99
    vs
    @4
    nfcv
    vt
    @33
    @4
    nfcsb1v
    vt
    @33
    @4
    csbeq1a
    cbvmpt
    @96
    syl5eqelr
    mulcncf
    @55
    @100
    cnmbf
    sylancr
    itgabsnc
    @52
    vt
    @55
    @37
    @52
    @60
    wa
    #
    @4
    @77
    abscld
    @52
    vt
    @55
    @4
    cvv
    @103
    @2
    @3
    fvexd
    @85
    @97
    iblabsnc
    @103
    @4
    @77
    absge0d
    itgposval
    breqtrd
    @56
    @59
    @35
    @63
    @40
    cle
    @56
    @58
    @34
    cabs
    vt
    @55
    @33
    @4
    itgeq1
    fveq2d
    @56
    @62
    @39
    citg2
    @56
    vt
    cr
    @61
    @38
    @56
    @60
    @36
    @37
    cc0
    @55
    @33
    @2
    eleq2
    ifbid
    mpteq2dv
    fveq2d
    breq12d
    syl5ibcom
    sylbid
    rexlimdva
    syl5
    ralrimiv
    ftc1anc
    wph
    cF
    vx
    @9
    @13
    cmpt
    #
    @9
    cc
    ccncf
    co
    #
    wph
    vx
    @9
    cc
    cF
    wph
    cF
    @105
    wcel
    @9
    cc
    cF
    wf
    ftc2nc.f
    @9
    cc
    cF
    cncff
    syl
    #
    feqmptd
    #
    ftc2nc.f
    eqeltrrd
    cncfmpt2f
    wph
    cr
    @15
    cdv
    co
    #
    vx
    @1
    cc0
    cmpt
    #
    @1
    cc0
    csn
    cxp
    wph
    @108
    cr
    vx
    @1
    @14
    cmpt
    cdv
    co
    vx
    @1
    @10
    @3
    cfv
    #
    @110
    cmin
    co
    #
    cmpt
    @109
    wph
    vx
    @14
    cr
    cioo
    crn
    ctg
    cfv
    #
    @27
    @9
    @1
    @90
    wph
    ax-resscn
    a1i
    #
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @9
    cr
    wss
    ftc2nc.a
    ftc2nc.b
    cA
    cB
    iccssre
    syl2anc
    #
    wph
    @10
    @9
    wcel
    #
    wa
    #
    @12
    @13
    @118
    vt
    @11
    @4
    cvv
    @118
    @2
    @11
    wcel
    wa
    @2
    @3
    fvexd
    @118
    vt
    @11
    @1
    @4
    cvv
    @118
    @21
    @10
    cB
    cle
    wbr
    #
    @11
    @1
    wss
    @118
    cB
    wph
    @115
    @117
    ftc2nc.b
    adantr
    rexrd
    @118
    @10
    cr
    wcel
    #
    cA
    @10
    cle
    wbr
    #
    @119
    wph
    @117
    @120
    @121
    @119
    w3a
    #
    wph
    @114
    @115
    @117
    @122
    wb
    ftc2nc.a
    ftc2nc.b
    cA
    cB
    @10
    elicc2
    syl2anc
    biimpa
    simp3d
    cA
    @10
    cB
    iooss2
    syl2anc
    @11
    @78
    wcel
    @118
    cA
    @10
    ioombl
    a1i
    @118
    @64
    wa
    @2
    @3
    fvexd
    wph
    @82
    @117
    @84
    adantr
    iblss
    itgcl
    #
    wph
    @9
    cc
    @10
    cF
    @106
    ffvelrnda
    #
    subcld
    @27
    @28
    tgioo2
    #
    @28
    wph
    @114
    @115
    @9
    @112
    cnt
    cfv
    cfv
    @1
    wceq
    ftc2nc.a
    ftc2nc.b
    cA
    cB
    iccntr
    syl2anc
    #
    dvmptntr
    wph
    vx
    @12
    @110
    @13
    @110
    cr
    cc
    cc
    @1
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    @10
    @1
    wcel
    #
    wph
    @117
    @12
    cc
    wcel
    @1
    @9
    @10
    cA
    cB
    ioossicc
    sseli
    #
    @123
    sylan2
    wph
    @1
    cc
    @10
    @3
    @32
    ffvelrnda
    #
    wph
    cr
    @29
    cdv
    co
    @3
    cr
    vx
    @1
    @12
    cmpt
    cdv
    co
    vx
    @1
    @110
    cmpt
    #
    wph
    vx
    vt
    cA
    cB
    @3
    @29
    @30
    ftc2nc.a
    ftc2nc.b
    ftc2nc.le
    ftc2nc.c
    ftc2nc.i
    ftc1cnnc
    wph
    vx
    @12
    cr
    @112
    @27
    @9
    @1
    @113
    @116
    @123
    @125
    @28
    @126
    dvmptntr
    wph
    vx
    @1
    cc
    @3
    @32
    feqmptd
    #
    3eqtr3d
    @127
    wph
    @117
    @13
    cc
    wcel
    @128
    @124
    sylan2
    @129
    wph
    @3
    cr
    @104
    cdv
    co
    @130
    cr
    vx
    @1
    @13
    cmpt
    cdv
    co
    wph
    cF
    @104
    cr
    cdv
    @107
    oveq2d
    @131
    wph
    vx
    @13
    cr
    @112
    @27
    @9
    @1
    @113
    @116
    @124
    @125
    @28
    @126
    dvmptntr
    3eqtr3rd
    dvmptsub
    wph
    vx
    @1
    @111
    cc0
    wph
    @127
    wa
    @110
    @129
    subidd
    mpteq2dva
    3eqtrd
    vx
    @1
    cc0
    fconstmpt
    syl6eqr
    dveq0
    fveq1d
    wph
    @19
    @26
    @6
    wceq
    @25
    vx
    cB
    @14
    @6
    @9
    @15
    @10
    cB
    wceq
    #
    @12
    @5
    @13
    @0
    cmin
    @132
    @11
    @1
    wceq
    @12
    @5
    wceq
    @10
    cB
    cA
    cioo
    oveq2
    vt
    @11
    @1
    @4
    itgeq1
    syl
    @10
    cB
    cF
    fveq2
    oveq12d
    @15
    eqid
    #
    @5
    @0
    cmin
    ovex
    fvmpt
    syl
    eqtr3d
    wph
    cA
    @9
    wcel
    #
    @16
    @8
    wceq
    wph
    @20
    @21
    @22
    @134
    @23
    @24
    ftc2nc.le
    cA
    cB
    lbicc2
    syl3anc
    #
    vx
    cA
    @14
    @8
    @9
    @15
    @10
    cA
    wceq
    #
    @14
    cc0
    @7
    cmin
    co
    @8
    @136
    @12
    cc0
    @13
    @7
    cmin
    @136
    @12
    vt
    c0
    @4
    citg
    #
    cc0
    @136
    @11
    c0
    wceq
    @12
    @137
    wceq
    @136
    @11
    cA
    cA
    cioo
    co
    c0
    @10
    cA
    cA
    cioo
    oveq2
    cA
    iooid
    syl6eq
    vt
    @11
    c0
    @4
    itgeq1
    syl
    vt
    @4
    itg0
    syl6eq
    @10
    cA
    cF
    fveq2
    oveq12d
    @7
    df-neg
    syl6eqr
    @133
    @7
    negex
    fvmpt
    syl
    3eqtr3d
    oveq2d
    wph
    @0
    @5
    wph
    @9
    cc
    cB
    cF
    @106
    @25
    ffvelrnd
    #
    wph
    vt
    @1
    @4
    cvv
    wph
    @64
    wa
    @2
    @3
    fvexd
    @84
    itgcl
    pncan3d
    wph
    @0
    @7
    @138
    wph
    @9
    cc
    cA
    cF
    @106
    @135
    ffvelrnd
    negsubd
    3eqtr3d
end
