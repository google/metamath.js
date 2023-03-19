include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "wcel.mm"
include "ccom.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "wn.mm"
include "w3a.mm"
include "wrex.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "cpmtr.mm"
include "cfv.mm"
include "eqid.mm"
include "pmtrfinv.mm"
include "syl.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "imp.mm"
include "orcd.mm"
include "wne.mm"
include "ccnv.mm"
include "pmtrfcnv.mm"
include "eqcomd.mm"
include "coeq2d.mm"
include "wf1o.mm"
include "pmtrff1o.mm"
include "pmtrfconj.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ad2antrr.mm"
include "coass.mm"
include "wf.mm"
include "f1of.mm"
include "fco.mm"
include "fcoi1.mm"
include "eqtrd.mm"
include "syl5req.mm"
include "cima.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "pmtrfb.mm"
include "simp3bi.mm"
include "cfn.mm"
include "wss.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "wb.mm"
include "enfi.mm"
include "mpbiri.mm"
include "csn.mm"
include "cuni.mm"
include "cpr.mm"
include "en2eleq.mm"
include "simprl.mm"
include "wfn.mm"
include "f1ofn.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "simprr.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "cif.mm"
include "difss.mm"
include "dmss.mm"
include "f1odm.mm"
include "syl5sseq.mm"
include "sseldd.mm"
include "pmtrffv.mm"
include "iftrued.mm"
include "imaco.mm"
include "imaeq1d.mm"
include "resiima.mm"
include "syl5eqr.mm"
include "3eltr3d.mm"
include "prssi.mm"
include "eqsstrd.mm"
include "ensymd.mm"
include "entr.mm"
include "fisseneq.mm"
include "f1otrspeq.mm"
include "syl22anc.mm"
include "expr.mm"
include "necon3ad.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "f1omvdconj.mm"
include "eleq2d.mm"
include "mtbird.mm"
include "eqeq2d.mm"
include "difeq1.mm"
include "notbid.mm"
include "3anbi13d.mm"
include "coeq2.mm"
include "3anbi12d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "olcd.mm"
include "pm2.61dane.mm"
include "coeq1d.mm"
include "fcoi2.mm"
include "eqtr2d.mm"
include "syl6eq.mm"
include "fnelnfp.mm"
include "necon2bbid.mm"
include "biimpar.mm"
include "eqeltrrd.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "pm2.61dan.mm"

theorem psgnunilem1
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  assume psgnunilem1.t: |- T = ran ( pmTrsp ` D )
  assume psgnunilem1.d: |- ( ph -> D e. V )
  assume psgnunilem1.p: |- ( ph -> P e. T )
  assume psgnunilem1.q: |- ( ph -> Q e. T )
  assume psgnunilem1.a: |- ( ph -> A e. dom ( P \ _I ) )

  disjoint r s
  disjoint A r
  disjoint A s
  disjoint P r
  disjoint P s
  disjoint Q r
  disjoint Q s
  disjoint T r
  disjoint T s
  assert |- ( ph -> ( ( P o. Q ) = ( _I |` D ) \/ E. r e. T E. s e. T ( ( P o. Q ) = ( r o. s ) /\ A e. dom ( s \ _I ) /\ -. A e. dom ( r \ _I ) ) ) )

  proof
    wph
    cA
    cQ
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    cP
    cQ
    ccom
    #
    cid
    cD
    cres
    #
    wceq
    #
    @3
    vr
    cv
    #
    vs
    cv
    #
    ccom
    #
    wceq
    #
    cA
    @7
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    cA
    @6
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    w3a
    #
    vs
    cT
    wrex
    vr
    cT
    wrex
    #
    wo
    #
    wph
    @2
    wa
    #
    @19
    cP
    cQ
    @20
    cP
    cQ
    wceq
    #
    wa
    @5
    @18
    @20
    @21
    @5
    wph
    @21
    @5
    wi
    @2
    wph
    @5
    @21
    cQ
    cQ
    ccom
    #
    @4
    wceq
    #
    wph
    cQ
    cT
    wcel
    #
    @23
    psgnunilem1.q
    cD
    cT
    cD
    cpmtr
    cfv
    #
    cQ
    @25
    eqid
    #
    psgnunilem1.t
    pmtrfinv
    syl
    #
    @21
    @3
    @22
    @4
    cP
    cQ
    cQ
    coeq1
    eqeq1d
    syl5ibrcom
    adantr
    imp
    orcd
    @20
    cP
    cQ
    wne
    #
    wa
    #
    @18
    @5
    @29
    @3
    cP
    ccom
    #
    cT
    wcel
    #
    cP
    cT
    wcel
    #
    @3
    @30
    cP
    ccom
    #
    wceq
    #
    cA
    cP
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    cA
    @30
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    @18
    wph
    @31
    @2
    @28
    wph
    @30
    @3
    cP
    ccnv
    #
    ccom
    #
    cT
    wph
    cP
    @42
    @3
    wph
    @42
    cP
    wph
    @32
    @42
    cP
    wceq
    psgnunilem1.p
    cD
    cT
    @25
    cP
    @26
    psgnunilem1.t
    pmtrfcnv
    syl
    eqcomd
    coeq2d
    #
    wph
    @24
    cD
    cD
    cP
    wf1o
    #
    @43
    cT
    wcel
    psgnunilem1.q
    wph
    @32
    @45
    psgnunilem1.p
    cD
    cT
    @25
    cP
    @26
    psgnunilem1.t
    pmtrff1o
    syl
    #
    cD
    cT
    @25
    cQ
    cP
    @26
    psgnunilem1.t
    pmtrfconj
    syl2anc
    eqeltrd
    ad2antrr
    wph
    @32
    @2
    @28
    psgnunilem1.p
    ad2antrr
    wph
    @34
    @2
    @28
    wph
    @33
    @3
    cP
    cP
    ccom
    #
    ccom
    #
    @3
    @3
    cP
    cP
    coass
    wph
    @48
    @3
    @4
    ccom
    #
    @3
    wph
    @47
    @4
    @3
    wph
    @32
    @47
    @4
    wceq
    psgnunilem1.p
    cD
    cT
    @25
    cP
    @26
    psgnunilem1.t
    pmtrfinv
    syl
    #
    coeq2d
    wph
    cD
    cD
    @3
    wf
    #
    @49
    @3
    wceq
    wph
    cD
    cD
    cP
    wf
    #
    cD
    cD
    cQ
    wf
    #
    @51
    wph
    @45
    @52
    @46
    cD
    cD
    cP
    f1of
    syl
    #
    wph
    cD
    cD
    cQ
    wf1o
    #
    @53
    wph
    @24
    @55
    psgnunilem1.q
    cD
    cT
    @25
    cQ
    @26
    psgnunilem1.t
    pmtrff1o
    syl
    #
    cD
    cD
    cQ
    f1of
    syl
    #
    cD
    cD
    cD
    cP
    cQ
    fco
    syl2anc
    #
    cD
    cD
    @3
    fcoi1
    syl
    eqtrd
    syl5req
    ad2antrr
    wph
    @37
    @2
    @28
    psgnunilem1.a
    ad2antrr
    @29
    @40
    cA
    cP
    @1
    cima
    #
    wcel
    #
    @20
    @28
    @60
    wn
    @20
    @60
    cP
    cQ
    wph
    @2
    @60
    @21
    wph
    @2
    @60
    wa
    #
    wa
    #
    @45
    @55
    @36
    c2o
    cen
    wbr
    #
    @1
    @36
    wceq
    @21
    wph
    @45
    @61
    @46
    adantr
    wph
    @55
    @61
    @56
    adantr
    wph
    @63
    @61
    wph
    @32
    @63
    psgnunilem1.p
    @32
    cD
    cvv
    wcel
    #
    @45
    @63
    cD
    cT
    @25
    cP
    @26
    psgnunilem1.t
    pmtrfb
    simp3bi
    syl
    #
    adantr
    #
    @62
    @36
    @1
    @62
    @1
    cfn
    wcel
    #
    @36
    @1
    wss
    @36
    @1
    cen
    wbr
    #
    @36
    @1
    wceq
    wph
    @67
    @61
    wph
    @67
    c2o
    cfn
    wcel
    #
    c2o
    com
    wcel
    @69
    2onn
    c2o
    nnfi
    ax-mp
    wph
    @1
    c2o
    cen
    wbr
    #
    @67
    @69
    wb
    wph
    @24
    @70
    psgnunilem1.q
    @24
    @64
    @55
    @70
    cD
    cT
    @25
    cQ
    @26
    psgnunilem1.t
    pmtrfb
    simp3bi
    syl
    #
    @1
    c2o
    enfi
    syl
    mpbiri
    adantr
    @62
    @36
    cA
    @36
    cA
    csn
    cdif
    cuni
    #
    cpr
    #
    @1
    @62
    @37
    @63
    @36
    @73
    wceq
    wph
    @37
    @61
    psgnunilem1.a
    adantr
    @66
    @36
    cA
    en2eleq
    syl2anc
    @62
    @2
    @72
    @1
    wcel
    @73
    @1
    wss
    wph
    @2
    @60
    simprl
    @62
    cA
    cP
    cfv
    #
    cP
    @59
    cima
    #
    @72
    @1
    @62
    cP
    cD
    wfn
    #
    @59
    cD
    wss
    #
    @60
    @74
    @75
    wcel
    wph
    @76
    @61
    wph
    @45
    @76
    @46
    cD
    cD
    cP
    f1ofn
    syl
    adantr
    wph
    @77
    @61
    wph
    @52
    @77
    @54
    @52
    @59
    cP
    crn
    cD
    cP
    @1
    imassrn
    cD
    cD
    cP
    frn
    syl5ss
    syl
    adantr
    wph
    @2
    @60
    simprr
    cD
    @59
    cP
    cA
    fnfvima
    syl3anc
    wph
    @74
    @72
    wceq
    @61
    wph
    @74
    @37
    @72
    cA
    cif
    #
    @72
    wph
    @32
    cA
    cD
    wcel
    #
    @74
    @78
    wceq
    psgnunilem1.p
    wph
    @36
    cD
    cA
    wph
    cP
    cdm
    #
    @36
    cD
    @35
    cP
    wss
    @36
    @80
    wss
    cP
    cid
    difss
    @35
    cP
    dmss
    ax-mp
    wph
    @45
    @80
    cD
    wceq
    @46
    cD
    cD
    cP
    f1odm
    syl
    syl5sseq
    #
    psgnunilem1.a
    sseldd
    #
    cD
    @36
    cT
    @25
    cP
    cA
    @26
    psgnunilem1.t
    @36
    eqid
    pmtrffv
    syl2anc
    wph
    @37
    @72
    cA
    psgnunilem1.a
    iftrued
    eqtrd
    adantr
    wph
    @75
    @1
    wceq
    @61
    wph
    @75
    @47
    @1
    cima
    #
    @1
    cP
    cP
    @1
    imaco
    wph
    @83
    @4
    @1
    cima
    #
    @1
    wph
    @47
    @4
    @1
    @50
    imaeq1d
    wph
    @1
    cD
    wss
    #
    @84
    @1
    wceq
    wph
    @55
    @85
    @56
    @55
    cQ
    cdm
    #
    @1
    cD
    @0
    cQ
    wss
    @1
    @86
    wss
    cQ
    cid
    difss
    @0
    cQ
    dmss
    ax-mp
    cD
    cD
    cQ
    f1odm
    syl5sseq
    syl
    cD
    @1
    resiima
    syl
    eqtrd
    syl5eqr
    adantr
    3eltr3d
    cA
    @72
    @1
    prssi
    syl2anc
    eqsstrd
    wph
    @68
    @61
    wph
    @63
    c2o
    @1
    cen
    wbr
    @68
    @65
    wph
    @1
    c2o
    @71
    ensymd
    @36
    c2o
    @1
    entr
    syl2anc
    adantr
    @36
    @1
    fisseneq
    syl3anc
    eqcomd
    cD
    cP
    cQ
    f1otrspeq
    syl22anc
    expr
    necon3ad
    imp
    wph
    @40
    @60
    wb
    @2
    @28
    wph
    @39
    @59
    cA
    wph
    @39
    @43
    cid
    cdif
    #
    cdm
    #
    @59
    wph
    @38
    @87
    wph
    @30
    @43
    cid
    @44
    difeq1d
    dmeqd
    wph
    @53
    @45
    @88
    @59
    wceq
    @57
    @46
    cD
    cQ
    cP
    f1omvdconj
    syl2anc
    eqtrd
    eleq2d
    ad2antrr
    mtbird
    @17
    @34
    @37
    @41
    w3a
    @3
    @30
    @7
    ccom
    #
    wceq
    #
    @12
    @41
    w3a
    vr
    vs
    @30
    cP
    cT
    cT
    @6
    @30
    wceq
    #
    @9
    @90
    @16
    @41
    @12
    @91
    @8
    @89
    @3
    @6
    @30
    @7
    coeq1
    eqeq2d
    @91
    @15
    @40
    @91
    @14
    @39
    cA
    @91
    @13
    @38
    @6
    @30
    cid
    difeq1
    dmeqd
    eleq2d
    notbid
    3anbi13d
    @7
    cP
    wceq
    #
    @90
    @34
    @12
    @37
    @41
    @92
    @89
    @33
    @3
    @7
    cP
    @30
    coeq2
    eqeq2d
    @92
    @11
    @36
    cA
    @92
    @10
    @35
    @7
    cP
    cid
    difeq1
    dmeqd
    eleq2d
    3anbi12d
    rspc2ev
    syl113anc
    olcd
    pm2.61dane
    wph
    @2
    wn
    #
    wa
    #
    @18
    @5
    @94
    @24
    cQ
    @3
    ccom
    #
    cT
    wcel
    #
    @3
    cQ
    @95
    ccom
    #
    wceq
    #
    cA
    @95
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    @93
    @18
    wph
    @24
    @93
    psgnunilem1.q
    adantr
    wph
    @96
    @93
    wph
    @95
    cQ
    cP
    ccom
    #
    cQ
    ccnv
    #
    ccom
    #
    cT
    wph
    @95
    @102
    cQ
    ccom
    @104
    cQ
    cP
    cQ
    coass
    wph
    cQ
    @103
    @102
    wph
    @103
    cQ
    wph
    @24
    @103
    cQ
    wceq
    psgnunilem1.q
    cD
    cT
    @25
    cQ
    @26
    psgnunilem1.t
    pmtrfcnv
    syl
    eqcomd
    coeq2d
    syl5eqr
    #
    wph
    @32
    @55
    @104
    cT
    wcel
    psgnunilem1.p
    @56
    cD
    cT
    @25
    cP
    cQ
    @26
    psgnunilem1.t
    pmtrfconj
    syl2anc
    eqeltrd
    adantr
    wph
    @98
    @93
    wph
    @3
    @22
    @3
    ccom
    #
    @97
    wph
    @106
    @4
    @3
    ccom
    #
    @3
    wph
    @22
    @4
    @3
    @27
    coeq1d
    wph
    @51
    @107
    @3
    wceq
    @58
    cD
    cD
    @3
    fcoi2
    syl
    eqtr2d
    cQ
    cQ
    @3
    coass
    syl6eq
    adantr
    @94
    cA
    cQ
    @36
    cima
    #
    @100
    @94
    cA
    cQ
    cfv
    #
    cA
    @108
    wph
    @109
    cA
    wceq
    @93
    wph
    @2
    @109
    cA
    wph
    cQ
    cD
    wfn
    #
    @79
    @2
    @109
    cA
    wne
    wb
    wph
    @55
    @110
    @56
    cD
    cD
    cQ
    f1ofn
    syl
    #
    @82
    cD
    cQ
    cA
    fnelnfp
    syl2anc
    necon2bbid
    biimpar
    wph
    @109
    @108
    wcel
    #
    @93
    wph
    @110
    @36
    cD
    wss
    @37
    @112
    @111
    @81
    psgnunilem1.a
    cD
    @36
    cQ
    cA
    fnfvima
    syl3anc
    adantr
    eqeltrrd
    wph
    @100
    @108
    wceq
    @93
    wph
    @100
    @104
    cid
    cdif
    #
    cdm
    #
    @108
    wph
    @99
    @113
    wph
    @95
    @104
    cid
    @105
    difeq1d
    dmeqd
    wph
    @52
    @55
    @114
    @108
    wceq
    @54
    @56
    cD
    cP
    cQ
    f1omvdconj
    syl2anc
    eqtrd
    adantr
    eleqtrrd
    wph
    @93
    simpr
    @17
    @98
    @101
    @93
    w3a
    @3
    cQ
    @7
    ccom
    #
    wceq
    #
    @12
    @93
    w3a
    vr
    vs
    cQ
    @95
    cT
    cT
    @6
    cQ
    wceq
    #
    @9
    @116
    @16
    @93
    @12
    @117
    @8
    @115
    @3
    @6
    cQ
    @7
    coeq1
    eqeq2d
    @117
    @15
    @2
    @117
    @14
    @1
    cA
    @117
    @13
    @0
    @6
    cQ
    cid
    difeq1
    dmeqd
    eleq2d
    notbid
    3anbi13d
    @7
    @95
    wceq
    #
    @116
    @98
    @12
    @101
    @93
    @118
    @115
    @97
    @3
    @7
    @95
    cQ
    coeq2
    eqeq2d
    @118
    @11
    @100
    cA
    @118
    @10
    @99
    @7
    @95
    cid
    difeq1
    dmeqd
    eleq2d
    3anbi12d
    rspc2ev
    syl113anc
    olcd
    pm2.61dan
end
