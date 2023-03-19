include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "cpw.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wf1o.mm"
include "csdm.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "syl.mm"
include "pwexg.mm"
include "f1oeng.mm"
include "syl2anc.mm"
include "ensym.mm"
include "wn.mm"
include "c2o.mm"
include "cdom.mm"
include "cfn.mm"
include "wpss.mm"
include "com.mm"
include "canth2g.mm"
include "wb.mm"
include "sdomen2.mm"
include "mpbid.mm"
include "sdomnen.mm"
include "ccrd.mm"
include "cdm.mm"
include "con0.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "wss.mm"
include "wceq.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wf.mm"
include "cin.mm"
include "w3a.mm"
include "ccom.mm"
include "cdif.mm"
include "cres.mm"
include "cv.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "wfun.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "f1ofo.mm"
include "wfn.mm"
include "f1ofn.mm"
include "fnresdm.mm"
include "foeq1.mm"
include "4syl.mm"
include "mpbird.mm"
include "cop.mm"
include "fvex.mm"
include "f1osng.mm"
include "sylancl.mm"
include "pwidg.mm"
include "fnressn.mm"
include "f1oeq1.mm"
include "resdif.mm"
include "syl3anc.mm"
include "f1oco.mm"
include "resco.mm"
include "sylibr.mm"
include "f1of.mm"
include "wa.mm"
include "wne.mm"
include "0elpw.mm"
include "a1i.mm"
include "sdom0.mm"
include "breq2.mm"
include "mtbii.mm"
include "necon2ai.mm"
include "ad2antrr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simplr.mm"
include "simpr.mm"
include "neqned.mm"
include "ifclda.mm"
include "eqid.mm"
include "fmptd.mm"
include "fco.mm"
include "crn.mm"
include "frn.mm"
include "cores.mm"
include "syl6eqr.mm"
include "feq1d.mm"
include "inss1.mm"
include "canth4.mm"
include "simp1d.mm"
include "wi.mm"
include "simp2d.mm"
include "pssned.mm"
include "necomd.mm"
include "simp3d.mm"
include "fveq1i.mm"
include "3eqtr3g.mm"
include "elpw2g.mm"
include "fvco3.mm"
include "pssssd.mm"
include "sstrd.mm"
include "3eqtr3d.mm"
include "adantr.mm"
include "ifcl.mm"
include "sylancr.mm"
include "eqeq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "fvmptg.mm"
include "pssne.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "sylan9eq.mm"
include "fveq2d.mm"
include "sspsstr.mm"
include "sylan.mm"
include "eqtrd.mm"
include "anim12i.mm"
include "fvres.mm"
include "3eqtr4d.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "npss.mm"
include "sylib.mm"
include "wwe.mm"
include "wex.mm"
include "wral.mm"
include "cxp.mm"
include "pm3.2i.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "fpwwe.mm"
include "mpbiri.mm"
include "simpld.mm"
include "fpwwelem.mm"
include "simprd.mm"
include "weeq1.mm"
include "spcev.mm"
include "ween.mm"
include "eqeltrrd.mm"
include "domtri2.mm"
include "infcda1.mm"
include "syl6bir.mm"
include "syl6.mm"
include "mt3d.mm"
include "2onn.mm"
include "nnsdom.mm"
include "cdafi.mm"
include "isfinite.mm"
include "cun.mm"
include "csuc.mm"
include "sssucid.mm"
include "df-2o.mm"
include "sseqtr4i.mm"
include "xpss1.mm"
include "unss2.mm"
include "mp1i.mm"
include "ssun2.mm"
include "1onn.mm"
include "elexi.mm"
include "sucid.mm"
include "eleqtrri.mm"
include "snid.mm"
include "opelxpi.mm"
include "mp2an.mm"
include "sselii.mm"
include "wo.mm"
include "1n0.mm"
include "neii.mm"
include "opelxp2.mm"
include "elsni.mm"
include "mto.mm"
include "word.mm"
include "nnord.mm"
include "ordirr.mm"
include "mp2b.mm"
include "opelxp1.mm"
include "pm3.2ni.mm"
include "elun.mm"
include "mtbir.mm"
include "ssnelpss.mm"
include "mp2ani.mm"
include "cdaval.mm"
include "psseq12d.mm"
include "php3.mm"
include "canthp1lem1.mm"
include "sdomdomtr.mm"
include "pm2.65i.mm"

theorem canthp1lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let vr: setvar r
  assume canthp1lem2.1: |- ( ph -> 1o ~< A )
  assume canthp1lem2.2: |- ( ph -> F : ~P A -1-1-onto-> ( A +c 1o ) )
  assume canthp1lem2.3: |- ( ph -> G : ( ( A +c 1o ) \ { ( F ` A ) } ) -1-1-onto-> A )
  assume canthp1lem2.4: |- H = ( ( G o. F ) o. ( x e. ~P A |-> if ( x = A , (/) , x ) ) )
  assume canthp1lem2.5: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x ( H ` ( `' r " { y } ) ) = y ) ) }
  assume canthp1lem2.6: |- B = U. dom W

  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint H r
  disjoint H x
  disjoint H y
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint W r
  disjoint W x
  disjoint W y
  assert |- -. ph

  proof
    wph
    cA
    c1o
    ccda
    co
    #
    cA
    cpw
    #
    cen
    wbr
    #
    wph
    @1
    @0
    cen
    wbr
    #
    @2
    wph
    @1
    cvv
    wcel
    #
    @1
    @0
    cF
    wf1o
    #
    @3
    wph
    cA
    cvv
    wcel
    #
    @4
    wph
    c1o
    cA
    csdm
    wbr
    #
    @6
    canthp1lem2.1
    c1o
    cA
    csdm
    relsdom
    brrelex2i
    syl
    #
    cA
    cvv
    pwexg
    syl
    canthp1lem2.2
    @1
    @0
    cvv
    cF
    f1oeng
    syl2anc
    #
    @1
    @0
    ensym
    syl
    wph
    @0
    @1
    csdm
    wbr
    #
    @2
    wn
    wph
    @0
    cA
    c2o
    ccda
    co
    #
    csdm
    wbr
    #
    @11
    @1
    cdom
    wbr
    #
    @10
    wph
    @11
    cfn
    wcel
    #
    @0
    @11
    wpss
    #
    @12
    wph
    @11
    com
    csdm
    wbr
    #
    @14
    wph
    cA
    com
    csdm
    wbr
    #
    c2o
    com
    csdm
    wbr
    #
    @16
    wph
    @17
    cA
    @0
    cen
    wbr
    #
    wph
    cA
    @0
    csdm
    wbr
    #
    @19
    wn
    wph
    cA
    @1
    csdm
    wbr
    #
    @20
    wph
    @6
    @21
    @8
    cA
    cvv
    canth2g
    syl
    wph
    @3
    @21
    @20
    wb
    @9
    @1
    @0
    cA
    sdomen2
    syl
    mpbid
    cA
    @0
    sdomnen
    syl
    wph
    @17
    wn
    #
    @0
    cA
    cen
    wbr
    #
    @19
    wph
    @22
    com
    cA
    cdom
    wbr
    #
    @23
    wph
    com
    ccrd
    cdm
    #
    wcel
    #
    cA
    @25
    wcel
    @24
    @22
    wb
    com
    con0
    wcel
    @26
    omelon
    com
    onenon
    ax-mp
    wph
    cB
    cA
    @25
    wph
    cB
    cA
    wss
    #
    cB
    cA
    wceq
    #
    wph
    @27
    cB
    cW
    cfv
    #
    ccnv
    #
    cB
    cH
    cfv
    #
    csn
    cima
    #
    cB
    wpss
    #
    @31
    @32
    cH
    cfv
    #
    wceq
    #
    wph
    @6
    @1
    cA
    cH
    wf
    #
    @1
    @25
    cin
    #
    @1
    wss
    #
    @27
    @33
    @35
    w3a
    @8
    wph
    @1
    cA
    cG
    cF
    ccom
    #
    @1
    cA
    csn
    #
    cdif
    #
    cres
    #
    vx
    @1
    vx
    cv
    #
    cA
    wceq
    #
    c0
    @43
    cif
    #
    cmpt
    #
    ccom
    #
    wf
    #
    @36
    wph
    @41
    cA
    @42
    wf
    #
    @1
    @41
    @46
    wf
    #
    @48
    wph
    @41
    cA
    @42
    wf1o
    #
    @49
    wph
    @41
    cA
    cG
    cF
    @41
    cres
    #
    ccom
    #
    wf1o
    #
    @51
    wph
    @0
    cA
    cF
    cfv
    #
    csn
    #
    cdif
    #
    cA
    cG
    wf1o
    @41
    @57
    @52
    wf1o
    #
    @54
    canthp1lem2.3
    wph
    cF
    ccnv
    wfun
    #
    @1
    @0
    cF
    @1
    cres
    #
    wfo
    #
    @40
    @56
    cF
    @40
    cres
    #
    wfo
    #
    @58
    wph
    @5
    @59
    canthp1lem2.2
    @5
    @1
    @0
    cF
    wfo
    #
    @59
    @1
    @0
    cF
    dff1o3
    simprbi
    syl
    wph
    @61
    @64
    wph
    @5
    @64
    canthp1lem2.2
    @1
    @0
    cF
    f1ofo
    syl
    wph
    @5
    cF
    @1
    wfn
    #
    @60
    cF
    wceq
    @61
    @64
    wb
    canthp1lem2.2
    @1
    @0
    cF
    f1ofn
    #
    @1
    cF
    fnresdm
    @1
    @0
    @60
    cF
    foeq1
    4syl
    mpbird
    wph
    @40
    @56
    @62
    wf1o
    #
    @63
    wph
    @67
    @40
    @56
    cA
    @55
    cop
    csn
    #
    wf1o
    #
    wph
    @6
    @55
    cvv
    wcel
    @69
    @8
    cA
    cF
    fvex
    cA
    @55
    cvv
    cvv
    f1osng
    sylancl
    wph
    @62
    @68
    wceq
    #
    @67
    @69
    wb
    wph
    @65
    cA
    @1
    wcel
    #
    @70
    wph
    @5
    @65
    canthp1lem2.2
    @66
    syl
    wph
    @6
    @71
    @8
    cA
    cvv
    pwidg
    syl
    @1
    cA
    cF
    fnressn
    syl2anc
    @40
    @56
    @62
    @68
    f1oeq1
    syl
    mpbird
    @40
    @56
    @62
    f1ofo
    syl
    @1
    @40
    @0
    @56
    cF
    resdif
    syl3anc
    @41
    @57
    cA
    cG
    @52
    f1oco
    syl2anc
    @42
    @53
    wceq
    @51
    @54
    wb
    cG
    cF
    @41
    resco
    @41
    cA
    @42
    @53
    f1oeq1
    ax-mp
    sylibr
    #
    @41
    cA
    @42
    f1of
    syl
    wph
    vx
    @1
    @45
    @41
    @46
    wph
    @43
    @1
    wcel
    #
    wa
    #
    @44
    c0
    @43
    @41
    @74
    @44
    wa
    #
    c0
    @1
    wcel
    #
    c0
    cA
    wne
    #
    c0
    @41
    wcel
    @76
    @75
    cA
    0elpw
    #
    a1i
    wph
    @77
    @73
    @44
    wph
    @7
    @77
    canthp1lem2.1
    @7
    c0
    cA
    c0
    cA
    wceq
    c1o
    c0
    csdm
    wbr
    @7
    c1o
    sdom0
    c0
    cA
    c1o
    csdm
    breq2
    mtbii
    necon2ai
    syl
    ad2antrr
    c0
    @1
    cA
    eldifsn
    sylanbrc
    @74
    @44
    wn
    #
    wa
    #
    @73
    @43
    cA
    wne
    @43
    @41
    wcel
    wph
    @73
    @79
    simplr
    @80
    @43
    cA
    @74
    @79
    simpr
    neqned
    @43
    @1
    cA
    eldifsn
    sylanbrc
    ifclda
    @46
    eqid
    #
    fmptd
    #
    @1
    @41
    cA
    @42
    @46
    fco
    syl2anc
    wph
    @1
    cA
    @47
    cH
    wph
    @47
    @39
    @46
    ccom
    #
    cH
    wph
    @46
    crn
    @41
    wss
    #
    @47
    @83
    wceq
    wph
    @50
    @84
    @82
    @1
    @41
    @46
    frn
    syl
    @39
    @46
    @41
    cores
    syl
    canthp1lem2.4
    syl6eqr
    feq1d
    mpbid
    #
    @38
    wph
    @1
    @25
    inss1
    #
    a1i
    vx
    vy
    cA
    cB
    @32
    @1
    cH
    cvv
    cW
    vr
    canthp1lem2.5
    canthp1lem2.6
    @32
    eqid
    canth4
    syl3anc
    #
    simp1d
    #
    wph
    cB
    cA
    wpss
    #
    wn
    #
    @27
    @28
    wi
    wph
    cB
    @32
    wne
    @90
    wph
    @32
    cB
    wph
    @32
    cB
    wph
    @27
    @33
    @35
    @87
    simp2d
    #
    pssned
    necomd
    wph
    @89
    cB
    @32
    wph
    @89
    cB
    @32
    wceq
    #
    wph
    @89
    wa
    #
    cB
    @42
    cfv
    #
    @32
    @42
    cfv
    #
    wceq
    #
    @92
    @93
    cB
    @39
    cfv
    #
    @32
    @39
    cfv
    #
    @94
    @95
    @93
    cB
    @46
    cfv
    #
    @39
    cfv
    #
    @32
    @46
    cfv
    #
    @39
    cfv
    #
    @97
    @98
    wph
    @100
    @102
    wceq
    @89
    wph
    cB
    @83
    cfv
    #
    @32
    @83
    cfv
    #
    @100
    @102
    wph
    @31
    @34
    @103
    @104
    wph
    @27
    @33
    @35
    @87
    simp3d
    cB
    cH
    @83
    canthp1lem2.4
    fveq1i
    @32
    cH
    @83
    canthp1lem2.4
    fveq1i
    3eqtr3g
    wph
    @50
    cB
    @1
    wcel
    #
    @103
    @100
    wceq
    @82
    wph
    @105
    @27
    @88
    wph
    @6
    @105
    @27
    wb
    @8
    cB
    cA
    cvv
    elpw2g
    syl
    mpbird
    #
    @1
    @41
    cB
    @39
    @46
    fvco3
    syl2anc
    wph
    @50
    @32
    @1
    wcel
    #
    @104
    @102
    wceq
    @82
    wph
    @107
    @32
    cA
    wss
    #
    wph
    @32
    cB
    cA
    wph
    @32
    cB
    @91
    pssssd
    #
    @88
    sstrd
    wph
    @6
    @107
    @108
    wb
    @8
    @32
    cA
    cvv
    elpw2g
    syl
    mpbird
    #
    @1
    @41
    @32
    @39
    @46
    fvco3
    syl2anc
    3eqtr3d
    adantr
    @93
    @99
    cB
    @39
    wph
    @89
    @99
    @28
    c0
    cB
    cif
    #
    cB
    wph
    @105
    @111
    @1
    wcel
    #
    @99
    @111
    wceq
    @106
    wph
    @76
    @105
    @112
    @78
    @106
    @28
    c0
    cB
    @1
    ifcl
    sylancr
    vx
    cB
    @45
    @111
    @1
    @1
    @46
    @43
    cB
    wceq
    #
    @44
    @28
    @43
    cB
    c0
    @43
    cB
    cA
    eqeq1
    @113
    id
    ifbieq2d
    @81
    fvmptg
    syl2anc
    @89
    @28
    c0
    cB
    @89
    cB
    cA
    cB
    cA
    pssne
    #
    neneqd
    iffalsed
    sylan9eq
    fveq2d
    @93
    @101
    @32
    @39
    @93
    @101
    @32
    cA
    wceq
    #
    c0
    @32
    cif
    #
    @32
    wph
    @101
    @116
    wceq
    #
    @89
    wph
    @107
    @116
    @1
    wcel
    #
    @117
    @110
    wph
    @76
    @107
    @118
    @78
    @110
    @115
    c0
    @32
    @1
    ifcl
    sylancr
    vx
    @32
    @45
    @116
    @1
    @1
    @46
    @43
    @32
    wceq
    #
    @44
    @115
    @43
    @32
    c0
    @43
    @32
    cA
    eqeq1
    @119
    id
    ifbieq2d
    @81
    fvmptg
    syl2anc
    adantr
    @93
    @115
    c0
    @32
    @93
    @32
    cA
    @93
    @32
    cA
    wph
    @32
    cB
    wss
    @89
    @32
    cA
    wpss
    @109
    @32
    cB
    cA
    sspsstr
    sylan
    pssned
    #
    neneqd
    iffalsed
    eqtrd
    fveq2d
    3eqtr3d
    @93
    cB
    @41
    wcel
    #
    @94
    @97
    wceq
    @93
    @105
    cB
    cA
    wne
    #
    wa
    @121
    wph
    @105
    @89
    @122
    @106
    @114
    anim12i
    cB
    @1
    cA
    eldifsn
    sylibr
    #
    cB
    @41
    @39
    fvres
    syl
    @93
    @32
    @41
    wcel
    #
    @95
    @98
    wceq
    @93
    @107
    @32
    cA
    wne
    @124
    wph
    @107
    @89
    @110
    adantr
    @120
    @32
    @1
    cA
    eldifsn
    sylanbrc
    #
    @32
    @41
    @39
    fvres
    syl
    3eqtr4d
    @93
    @41
    cA
    @42
    wf1
    #
    @121
    @124
    @96
    @92
    wb
    wph
    @126
    @89
    wph
    @51
    @126
    @72
    @41
    cA
    @42
    f1of1
    syl
    adantr
    @123
    @125
    @41
    cA
    cB
    @32
    @42
    f1fveq
    syl12anc
    mpbid
    ex
    necon3ad
    mpd
    cB
    cA
    npss
    sylib
    mpd
    wph
    cB
    vr
    cv
    #
    wwe
    #
    vr
    wex
    #
    cB
    @25
    wcel
    wph
    cB
    @29
    wwe
    #
    @129
    wph
    @130
    @30
    vy
    cv
    #
    csn
    cima
    cH
    cfv
    @131
    wceq
    vy
    cB
    wral
    #
    wph
    @27
    @29
    cB
    cB
    cxp
    wss
    wa
    #
    @130
    @132
    wa
    #
    wph
    cB
    @29
    cW
    wbr
    #
    @133
    @134
    wa
    wph
    @135
    @31
    cB
    wcel
    #
    wph
    @135
    @136
    wa
    cB
    cB
    wceq
    #
    @29
    @29
    wceq
    #
    wa
    @137
    @138
    cB
    eqid
    @29
    eqid
    pm3.2i
    wph
    vx
    vy
    cA
    @29
    cH
    cW
    cB
    cB
    vr
    canthp1lem2.5
    @8
    wph
    @36
    @73
    @43
    cH
    cfv
    cA
    wcel
    @43
    @37
    wcel
    @85
    @37
    @1
    @43
    @86
    sseli
    @1
    cA
    @43
    cH
    ffvelrn
    syl2an
    canthp1lem2.6
    fpwwe
    mpbiri
    simpld
    wph
    vx
    vy
    cA
    @29
    cH
    cW
    cB
    vr
    canthp1lem2.5
    @8
    fpwwelem
    mpbid
    simprd
    simpld
    @128
    @130
    vr
    @29
    cB
    cW
    fvex
    cB
    @127
    @29
    weeq1
    spcev
    syl
    cB
    vr
    ween
    sylibr
    eqeltrrd
    com
    cA
    domtri2
    sylancr
    cA
    infcda1
    syl6bir
    @0
    cA
    ensym
    syl6
    mt3d
    c2o
    com
    wcel
    #
    @18
    2onn
    c2o
    nnsdom
    ax-mp
    cA
    c2o
    cdafi
    sylancl
    @11
    isfinite
    sylibr
    wph
    @15
    cA
    c0
    csn
    #
    cxp
    #
    c1o
    c1o
    csn
    #
    cxp
    #
    cun
    #
    @141
    c2o
    @142
    cxp
    #
    cun
    #
    wpss
    #
    wph
    @144
    @146
    wss
    #
    @147
    @143
    @145
    wss
    #
    @148
    wph
    c1o
    c2o
    wss
    @149
    c1o
    c1o
    csuc
    #
    c2o
    c1o
    sssucid
    df-2o
    sseqtr4i
    c1o
    c2o
    @142
    xpss1
    ax-mp
    @143
    @145
    @141
    unss2
    mp1i
    @148
    c1o
    c1o
    cop
    #
    @146
    wcel
    @151
    @144
    wcel
    #
    wn
    @147
    @145
    @146
    @151
    @145
    @141
    ssun2
    c1o
    c2o
    wcel
    c1o
    @142
    wcel
    @151
    @145
    wcel
    c1o
    @150
    c2o
    c1o
    c1o
    com
    1onn
    elexi
    #
    sucid
    df-2o
    eleqtrri
    c1o
    @153
    snid
    c1o
    c1o
    c2o
    @142
    opelxpi
    mp2an
    sselii
    @152
    @151
    @141
    wcel
    #
    @151
    @143
    wcel
    #
    wo
    @154
    @155
    @154
    c1o
    c0
    wceq
    #
    c1o
    c0
    1n0
    neii
    @154
    c1o
    @140
    wcel
    @156
    c1o
    c1o
    cA
    @140
    opelxp2
    c1o
    c0
    elsni
    syl
    mto
    @155
    c1o
    c1o
    wcel
    #
    c1o
    com
    wcel
    #
    c1o
    word
    @157
    wn
    1onn
    c1o
    nnord
    c1o
    ordirr
    mp2b
    c1o
    c1o
    c1o
    @142
    opelxp1
    mto
    pm3.2ni
    @151
    @141
    @143
    elun
    mtbir
    @144
    @146
    @151
    ssnelpss
    mp2ani
    syl
    wph
    @0
    @144
    @11
    @146
    wph
    @6
    @158
    @0
    @144
    wceq
    @8
    1onn
    cA
    c1o
    cvv
    com
    cdaval
    sylancl
    wph
    @6
    @139
    @11
    @146
    wceq
    @8
    2onn
    cA
    c2o
    cvv
    com
    cdaval
    sylancl
    psseq12d
    mpbird
    @11
    @0
    php3
    syl2anc
    wph
    @7
    @13
    canthp1lem2.1
    cA
    canthp1lem1
    syl
    @0
    @11
    @1
    sdomdomtr
    syl2anc
    @0
    @1
    sdomnen
    syl
    pm2.65i
end
