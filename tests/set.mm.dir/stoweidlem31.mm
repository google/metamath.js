include "cv.mm"
include "crn.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "wex.mm"
include "cfn.mm"
include "fnchoice.mm"
include "syl.mm"
include "ccom.mm"
include "cvv.mm"
include "vex.mm"
include "cc0.mm"
include "cle.mm"
include "cdif.mm"
include "w3a.mm"
include "crab.mm"
include "cmpt.mm"
include "ssexd.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "coexg.mm"
include "sylancl.mm"
include "sylancr.mm"
include "adantr.mm"
include "wss.mm"
include "simprl.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nfrn.mm"
include "nffn.mm"
include "nfv.mm"
include "nfral.mm"
include "nfan.mm"
include "wrex.mm"
include "wceq.mm"
include "wb.mm"
include "fvelrnb.mm"
include "biimpa.mm"
include "nfra1.mm"
include "simp3.mm"
include "simp1ll.mm"
include "simplrr.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "3simpc.mm"
include "simpr.mm"
include "rabexg.mm"
include "a1d.mm"
include "ralrimi.mm"
include "fnmpt.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvrex.mm"
include "syl6bb.mm"
include "mpbid.mm"
include "nfcri.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "crp.mm"
include "sselda.mm"
include "rabeq2i.mm"
include "sylib.mm"
include "simprd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "breq2.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "breq1d.mm"
include "3anbi23d.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "nfne.mm"
include "rabid.mm"
include "sylibr.mm"
include "ne0i.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "eqnetrd.mm"
include "3adant3.mm"
include "eqnetrrd.mm"
include "3adant1r.mm"
include "3adant2.mm"
include "rspa.mm"
include "sylc.mm"
include "jca.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "simp1r.mm"
include "simpl.mm"
include "eleqtrd.mm"
include "elrabi.mm"
include "fveq1.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "3anbi123d.mm"
include "elrab.mm"
include "simprbi.mm"
include "simp1d.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "reximdai.mm"
include "idd.mm"
include "a1i.mm"
include "ex.mm"
include "dfss3.mm"
include "eleq1.mm"
include "cbvral.mm"
include "bitri.mm"
include "df-f.mm"
include "dffn3.mm"
include "wf1o.mm"
include "f1of.mm"
include "fco.mm"
include "fvco3.mm"
include "sylan.mm"
include "simpll.mm"
include "ffvelrnda.mm"
include "nf3an.mm"
include "nfim.mm"
include "3anbi3d.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "vtoclg1f.mm"
include "mpcom.mm"
include "eqeltrd.mm"
include "raleq.mm"
include "3anbi2d.mm"
include "rabbidv.mm"
include "fvmptg.mm"
include "eqtrd.mm"
include "adantlr.mm"
include "eleq2d.mm"
include "nfco.mm"
include "nfbr.mm"
include "nfrab.mm"
include "ralbid.mm"
include "elrabf.mm"
include "simp2d.mm"
include "syl6bi.mm"
include "ad3antrrr.mm"
include "sseldd.mm"
include "simp3d.mm"
include "r19.21bi.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "feq1.mm"
include "fveq1d.mm"
include "spcegv.mm"
include "exlimddv.mm"

theorem stoweidlem31
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vh: setvar h
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cJ: class J
  let cM: class M
  let cV: class V
  let cY: class Y
  let vb: setvar b
  let vl: setvar l
  let vu: setvar u
  let vz: setvar z
  let vk: setvar k
  assume stoweidlem31.1: |- F/ h ph
  assume stoweidlem31.2: |- F/ t ph
  assume stoweidlem31.3: |- F/ w ph
  assume stoweidlem31.4: |- Y = { h e. A | A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) }
  assume stoweidlem31.5: |- V = { w e. J | A. e e. RR+ E. h e. A ( A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) /\ A. t e. w ( h ` t ) < e /\ A. t e. ( T \ U ) ( 1 - e ) < ( h ` t ) ) }
  assume stoweidlem31.6: |- G = ( w e. R |-> { h e. A | ( A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) /\ A. t e. w ( h ` t ) < ( E / M ) /\ A. t e. ( T \ U ) ( 1 - ( E / M ) ) < ( h ` t ) ) } )
  assume stoweidlem31.7: |- ( ph -> R C_ V )
  assume stoweidlem31.8: |- ( ph -> M e. NN )
  assume stoweidlem31.9: |- ( ph -> v : ( 1 ... M ) -1-1-onto-> R )
  assume stoweidlem31.10: |- ( ph -> E e. RR+ )
  assume stoweidlem31.11: |- ( ph -> B C_ ( T \ U ) )
  assume stoweidlem31.12: |- ( ph -> V e. _V )
  assume stoweidlem31.13: |- ( ph -> A e. _V )
  assume stoweidlem31.14: |- ( ph -> ran G e. Fin )

  disjoint h i
  disjoint h t
  disjoint h v
  disjoint h w
  disjoint i t
  disjoint i v
  disjoint i w
  disjoint t v
  disjoint t w
  disjoint v w
  disjoint G i
  disjoint Y w
  disjoint i ph
  disjoint e h
  disjoint e t
  disjoint e w
  disjoint A e
  disjoint A h
  disjoint A t
  disjoint A w
  disjoint E e
  disjoint E h
  disjoint E t
  disjoint E w
  disjoint M e
  disjoint M h
  disjoint M t
  disjoint M w
  disjoint T e
  disjoint T h
  disjoint T w
  disjoint U e
  disjoint U h
  disjoint U w
  disjoint R h
  disjoint R t
  disjoint R w
  disjoint i x
  disjoint t x
  disjoint v x
  disjoint M i
  disjoint B x
  disjoint E x
  disjoint G x
  disjoint M x
  disjoint Y x
  disjoint b h
  disjoint b i
  disjoint b l
  disjoint b t
  disjoint b v
  disjoint b w
  disjoint h l
  disjoint i l
  disjoint l t
  disjoint l v
  disjoint l w
  disjoint b u
  disjoint u w
  disjoint b z
  disjoint h z
  disjoint l z
  disjoint t z
  disjoint G b
  disjoint G l
  disjoint Y b
  disjoint Y l
  disjoint b ph
  disjoint l ph
  disjoint l x
  disjoint M l
  disjoint B l
  disjoint E l
  disjoint G u
  disjoint R u
  disjoint Y z
  disjoint k x
  assert |- ( ph -> E. x ( x : ( 1 ... M ) --> Y /\ A. i e. ( 1 ... M ) ( A. t e. ( v ` i ) ( ( x ` i ) ` t ) < ( E / M ) /\ A. t e. B ( 1 - ( E / M ) ) < ( ( x ` i ) ` t ) ) ) )

  proof
    wph
    vl
    cv
    #
    cG
    crn
    #
    wfn
    #
    vb
    cv
    #
    c0
    wne
    #
    @3
    @0
    cfv
    #
    @3
    wcel
    #
    wi
    #
    vb
    @1
    wral
    #
    wa
    #
    c1
    cM
    cfz
    co
    #
    cY
    vx
    cv
    #
    wf
    #
    vt
    cv
    #
    vi
    cv
    #
    @11
    cfv
    #
    cfv
    #
    cE
    cM
    cdiv
    co
    #
    clt
    wbr
    #
    vt
    @14
    vv
    cv
    #
    cfv
    #
    wral
    #
    c1
    @17
    cmin
    co
    #
    @16
    clt
    wbr
    #
    vt
    cB
    wral
    #
    wa
    #
    vi
    @10
    wral
    #
    wa
    #
    vx
    wex
    #
    vl
    wph
    @1
    cfn
    wcel
    @9
    vl
    wex
    stoweidlem31.14
    vb
    @1
    vl
    fnchoice
    syl
    wph
    @9
    wa
    #
    @0
    cG
    @19
    ccom
    #
    ccom
    #
    cvv
    wcel
    #
    @10
    cY
    @31
    wf
    #
    @13
    @14
    @31
    cfv
    #
    cfv
    #
    @17
    clt
    wbr
    #
    vt
    @20
    wral
    #
    @22
    @35
    clt
    wbr
    #
    vt
    cB
    wral
    #
    wa
    #
    vi
    @10
    wral
    #
    wa
    #
    @28
    wph
    @32
    @9
    wph
    @0
    cvv
    wcel
    @30
    cvv
    wcel
    #
    @32
    vl
    vex
    wph
    cG
    cvv
    wcel
    @19
    cvv
    wcel
    @43
    wph
    cG
    vw
    cR
    cc0
    @13
    vh
    cv
    #
    cfv
    #
    cle
    wbr
    #
    @45
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @45
    @17
    clt
    wbr
    #
    vt
    vw
    cv
    #
    wral
    #
    @22
    @45
    clt
    wbr
    #
    vt
    cT
    cU
    cdif
    #
    wral
    #
    w3a
    #
    vh
    cA
    crab
    #
    cmpt
    #
    cvv
    stoweidlem31.6
    wph
    cR
    cvv
    wcel
    @58
    cvv
    wcel
    wph
    cR
    cV
    cvv
    stoweidlem31.12
    stoweidlem31.7
    ssexd
    vw
    cR
    @57
    cvv
    mptexg
    syl
    syl5eqel
    vv
    vex
    cG
    @19
    cvv
    cvv
    coexg
    sylancl
    @0
    @30
    cvv
    cvv
    coexg
    sylancr
    adantr
    @29
    @33
    @41
    @29
    @1
    cY
    @0
    wf
    #
    @10
    @1
    @30
    wf
    #
    @33
    @29
    @2
    @0
    crn
    #
    cY
    wss
    #
    @59
    wph
    @2
    @8
    simprl
    #
    @29
    @44
    cY
    wcel
    #
    vh
    @61
    wral
    #
    @62
    @29
    @64
    vh
    @61
    wph
    @9
    vh
    stoweidlem31.1
    @2
    @8
    vh
    vh
    @1
    @0
    vh
    @0
    nfcv
    #
    vh
    cG
    vh
    cG
    @58
    stoweidlem31.6
    vh
    vw
    cR
    @57
    vh
    cR
    nfcv
    @56
    vh
    cA
    nfrab1
    #
    nfmpt
    nfcxfr
    #
    nfrn
    #
    nffn
    @7
    vh
    vb
    @1
    @69
    @7
    vh
    nfv
    nfral
    nfan
    nfan
    @29
    @44
    @61
    wcel
    #
    @64
    @29
    @70
    wa
    #
    @64
    vb
    @1
    wrex
    #
    @64
    @71
    @5
    @44
    wceq
    #
    vb
    @1
    wrex
    #
    @72
    @29
    @70
    @74
    @29
    @2
    @70
    @74
    wb
    @63
    vb
    @1
    @44
    @0
    fvelrnb
    syl
    biimpa
    @71
    @73
    @64
    vb
    @1
    @29
    @70
    vb
    wph
    @9
    vb
    wph
    vb
    nfv
    #
    @2
    @8
    vb
    @2
    vb
    nfv
    @7
    vb
    @1
    nfra1
    #
    nfan
    nfan
    @70
    vb
    nfv
    nfan
    #
    @71
    @3
    @1
    wcel
    #
    @73
    @64
    @71
    @78
    @73
    w3a
    #
    @5
    @44
    cY
    @71
    @78
    @73
    simp3
    @79
    wph
    @8
    @78
    @5
    cY
    wcel
    #
    wph
    @9
    @70
    @78
    @73
    simp1ll
    @71
    @78
    @8
    @73
    wph
    @2
    @8
    @70
    simplrr
    3ad2ant1
    @71
    @78
    @73
    simp2
    wph
    @8
    @78
    w3a
    #
    @78
    @6
    wa
    #
    @3
    @57
    wceq
    #
    vw
    cR
    wrex
    #
    @80
    @81
    @78
    @6
    wph
    @8
    @78
    simp3
    #
    @81
    @8
    @78
    wa
    @4
    @6
    wph
    @8
    @78
    3simpc
    wph
    @78
    @4
    @8
    wph
    @78
    wa
    #
    @51
    cG
    cfv
    #
    @3
    wceq
    #
    vw
    cR
    wrex
    #
    @4
    @86
    @78
    @89
    wph
    @78
    simpr
    @86
    cG
    cR
    wfn
    #
    @78
    @89
    wb
    wph
    @90
    @78
    wph
    @57
    cvv
    wcel
    #
    vw
    cR
    wral
    @90
    wph
    @91
    vw
    cR
    stoweidlem31.3
    wph
    @91
    @51
    cR
    wcel
    #
    wph
    cA
    cvv
    wcel
    #
    @91
    stoweidlem31.13
    @56
    vh
    cA
    cvv
    rabexg
    #
    syl
    a1d
    ralrimi
    vw
    cR
    @57
    cG
    cvv
    stoweidlem31.6
    fnmpt
    syl
    #
    adantr
    @90
    @78
    vu
    cv
    #
    cG
    cfv
    #
    @3
    wceq
    #
    vu
    cR
    wrex
    @89
    vu
    cR
    @3
    cG
    fvelrnb
    @98
    @88
    vu
    vw
    cR
    vw
    @97
    @3
    vw
    @96
    cG
    vw
    cG
    @58
    stoweidlem31.6
    vw
    cR
    @57
    nfmpt1
    nfcxfr
    #
    vw
    @96
    nfcv
    nffv
    vw
    @3
    nfcv
    nfeq
    @88
    vu
    nfv
    @96
    @51
    wceq
    @97
    @87
    @3
    @96
    @51
    cG
    fveq2
    eqeq1d
    cbvrex
    syl6bb
    syl
    mpbid
    @86
    @88
    @4
    vw
    cR
    wph
    @78
    vw
    stoweidlem31.3
    vw
    vb
    @1
    vw
    cG
    @99
    nfrn
    nfcri
    #
    nfan
    @4
    vw
    nfv
    @86
    @92
    @88
    @4
    wph
    @92
    @88
    @4
    @78
    wph
    @92
    @88
    w3a
    @87
    @3
    c0
    wph
    @92
    @88
    simp3
    wph
    @92
    @87
    c0
    wne
    @88
    wph
    @92
    wa
    #
    @87
    @57
    c0
    @101
    @92
    @91
    @87
    @57
    wceq
    wph
    @92
    simpr
    @101
    @93
    @91
    wph
    @93
    @92
    stoweidlem31.13
    adantr
    @94
    syl
    vw
    cR
    @57
    cvv
    cG
    stoweidlem31.6
    fvmpt2
    syl2anc
    @101
    @56
    vh
    cA
    wrex
    #
    @57
    c0
    wne
    #
    @101
    @49
    @45
    ve
    cv
    #
    clt
    wbr
    #
    vt
    @51
    wral
    #
    c1
    @104
    cmin
    co
    #
    @45
    clt
    wbr
    #
    vt
    @54
    wral
    #
    w3a
    #
    vh
    cA
    wrex
    #
    ve
    crp
    wral
    #
    @17
    crp
    wcel
    #
    @102
    @101
    @51
    cJ
    wcel
    #
    @112
    @101
    @51
    cV
    wcel
    @114
    @112
    wa
    wph
    cR
    cV
    @51
    stoweidlem31.7
    sselda
    @112
    vw
    cV
    cJ
    stoweidlem31.5
    rabeq2i
    sylib
    simprd
    wph
    @113
    @92
    wph
    cE
    cM
    stoweidlem31.10
    wph
    cM
    stoweidlem31.8
    nnrpd
    rpdivcld
    adantr
    @111
    @102
    ve
    @17
    crp
    @104
    @17
    wceq
    #
    @110
    @56
    vh
    cA
    @115
    @106
    @52
    @109
    @55
    @49
    @115
    @105
    @50
    vt
    @51
    @104
    @17
    @45
    clt
    breq2
    ralbidv
    @115
    @108
    @53
    vt
    @54
    @115
    @107
    @22
    @45
    clt
    @104
    @17
    c1
    cmin
    oveq2
    breq1d
    ralbidv
    3anbi23d
    rexbidv
    rspccva
    syl2anc
    @101
    @56
    @103
    vh
    cA
    wph
    @92
    vh
    stoweidlem31.1
    @92
    vh
    nfv
    nfan
    vh
    @57
    c0
    @67
    vh
    c0
    nfcv
    nfne
    @101
    @44
    cA
    wcel
    #
    @56
    @103
    @101
    @116
    @56
    w3a
    #
    @44
    @57
    wcel
    #
    @103
    @117
    @116
    @56
    wa
    @118
    @101
    @116
    @56
    3simpc
    @56
    vh
    cA
    rabid
    sylibr
    @57
    @44
    ne0i
    syl
    3exp
    rexlimd
    mpd
    eqnetrd
    3adant3
    eqnetrrd
    3adant1r
    3exp
    rexlimd
    mpd
    3adant2
    @7
    vb
    @1
    rspa
    sylc
    #
    jca
    @81
    @78
    @84
    @85
    @3
    cvv
    wcel
    @78
    @84
    wb
    vb
    vex
    vw
    cR
    @57
    @3
    cG
    cvv
    stoweidlem31.6
    elrnmpt
    ax-mp
    sylib
    @82
    @83
    @80
    vw
    cR
    @78
    @6
    vw
    @100
    @6
    vw
    nfv
    nfan
    @80
    vw
    nfv
    @82
    @92
    @83
    @80
    @82
    @92
    @83
    w3a
    @6
    @83
    @80
    @78
    @6
    @92
    @83
    simp1r
    @82
    @92
    @83
    simp3
    @6
    @83
    wa
    #
    @5
    @49
    vh
    cA
    crab
    #
    cY
    @120
    @5
    @57
    wcel
    #
    @5
    @121
    wcel
    #
    @120
    @5
    @3
    @57
    @6
    @83
    simpl
    @6
    @83
    simpr
    eleqtrd
    @122
    @5
    cA
    wcel
    #
    cc0
    @13
    @5
    cfv
    #
    cle
    wbr
    #
    @125
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @123
    @56
    vh
    @5
    cA
    elrabi
    @122
    @129
    @125
    @17
    clt
    wbr
    #
    vt
    @51
    wral
    #
    @22
    @125
    clt
    wbr
    #
    vt
    @54
    wral
    #
    @122
    @124
    @129
    @131
    @133
    w3a
    #
    @56
    @134
    vh
    @5
    cA
    @44
    @5
    wceq
    #
    @49
    @129
    @52
    @131
    @55
    @133
    @135
    @48
    @128
    vt
    cT
    @135
    @46
    @126
    @47
    @127
    @135
    @45
    @125
    cc0
    cle
    @13
    @44
    @5
    fveq1
    #
    breq2d
    @135
    @45
    @125
    c1
    cle
    @136
    breq1d
    anbi12d
    ralbidv
    #
    @135
    @50
    @130
    vt
    @51
    @135
    @45
    @125
    @17
    clt
    @136
    breq1d
    ralbidv
    @135
    @53
    @132
    vt
    @54
    @135
    @45
    @125
    @22
    clt
    @136
    breq2d
    ralbidv
    3anbi123d
    elrab
    simprbi
    simp1d
    @49
    @129
    vh
    @5
    cA
    @137
    elrab
    sylanbrc
    syl
    stoweidlem31.4
    syl6eleqr
    syl2anc
    3exp
    rexlimd
    sylc
    syl3anc
    eqeltrrd
    3exp
    reximdai
    mpd
    @71
    @64
    @64
    vb
    @1
    @77
    @64
    vb
    nfv
    @78
    @64
    @64
    wi
    wi
    @71
    @78
    @64
    idd
    a1i
    rexlimd
    mpd
    ex
    ralrimi
    @62
    vz
    cv
    #
    cY
    wcel
    #
    vz
    @61
    wral
    @65
    vz
    @61
    cY
    dfss3
    @139
    @64
    vz
    vh
    @61
    vh
    vz
    cY
    vh
    cY
    @121
    stoweidlem31.4
    @49
    vh
    cA
    nfrab1
    nfcxfr
    nfcri
    @64
    vz
    nfv
    @138
    @44
    cY
    eleq1
    cbvral
    bitri
    sylibr
    @1
    cY
    @0
    df-f
    sylanbrc
    @29
    cR
    @1
    cG
    wf
    #
    @10
    cR
    @19
    wf
    #
    @60
    wph
    @140
    @9
    wph
    @90
    @140
    @95
    cR
    cG
    dffn3
    sylib
    adantr
    wph
    @141
    @9
    wph
    @10
    cR
    @19
    wf1o
    @141
    stoweidlem31.9
    @10
    cR
    @19
    f1of
    syl
    #
    adantr
    @10
    cR
    @1
    cG
    @19
    fco
    syl2anc
    #
    @10
    @1
    cY
    @0
    @30
    fco
    syl2anc
    @29
    @40
    vi
    @10
    @29
    @14
    @10
    wcel
    #
    wa
    #
    @37
    @39
    @145
    @34
    @14
    @30
    cfv
    #
    wcel
    #
    @37
    @145
    @34
    @146
    @0
    cfv
    #
    @146
    @29
    @60
    @144
    @34
    @148
    wceq
    @143
    @10
    @1
    @14
    @0
    @30
    fvco3
    sylan
    @145
    wph
    @8
    @146
    @1
    wcel
    #
    @148
    @146
    wcel
    #
    wph
    @9
    @144
    simpll
    wph
    @2
    @8
    @144
    simplrr
    @29
    @10
    @1
    @14
    @30
    @143
    ffvelrnda
    @149
    wph
    @8
    @149
    w3a
    #
    @150
    wph
    @8
    @149
    simp3
    @81
    @6
    wi
    @151
    @150
    wi
    vb
    @146
    @1
    @151
    @150
    vb
    wph
    @8
    @149
    vb
    @75
    @76
    @149
    vb
    nfv
    nf3an
    @150
    vb
    nfv
    nfim
    @3
    @146
    wceq
    #
    @81
    @151
    @6
    @150
    @152
    @78
    @149
    wph
    @8
    @3
    @146
    @1
    eleq1
    3anbi3d
    @152
    @5
    @148
    @3
    @146
    @3
    @146
    @0
    fveq2
    @152
    id
    eleq12d
    imbi12d
    @119
    vtoclg1f
    mpcom
    syl3anc
    eqeltrd
    #
    @145
    @147
    @34
    @49
    @50
    vt
    @20
    wral
    #
    @55
    w3a
    #
    vh
    cA
    crab
    #
    wcel
    #
    @37
    @145
    @146
    @156
    @34
    wph
    @144
    @146
    @156
    wceq
    @9
    wph
    @144
    wa
    #
    @146
    @20
    cG
    cfv
    #
    @156
    wph
    @141
    @144
    @146
    @159
    wceq
    @142
    @10
    cR
    @14
    cG
    @19
    fvco3
    sylan
    @158
    @20
    cR
    wcel
    @156
    cvv
    wcel
    #
    @159
    @156
    wceq
    wph
    @10
    cR
    @14
    @19
    @142
    ffvelrnda
    @158
    @93
    @160
    wph
    @93
    @144
    stoweidlem31.13
    adantr
    @155
    vh
    cA
    cvv
    rabexg
    syl
    vw
    @20
    @57
    @156
    cR
    cvv
    cG
    @51
    @20
    wceq
    #
    @56
    @155
    vh
    cA
    @161
    @52
    @154
    @49
    @55
    @50
    vt
    @51
    @20
    raleq
    3anbi2d
    rabbidv
    stoweidlem31.6
    fvmptg
    syl2anc
    eqtrd
    adantlr
    eleq2d
    #
    @157
    cc0
    @35
    cle
    wbr
    #
    @35
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @37
    @38
    vt
    @54
    wral
    #
    @157
    @34
    cA
    wcel
    @166
    @37
    @167
    w3a
    #
    @155
    @168
    vh
    @34
    cA
    vh
    @14
    @31
    vh
    @0
    @30
    @66
    vh
    cG
    @19
    @68
    vh
    @19
    nfcv
    nfco
    nfco
    vh
    @14
    nfcv
    nffv
    #
    vh
    cA
    nfcv
    @166
    @37
    @167
    vh
    @165
    vh
    vt
    cT
    vh
    cT
    nfcv
    @163
    @164
    vh
    vh
    cc0
    @35
    cle
    vh
    cc0
    nfcv
    vh
    cle
    nfcv
    #
    vh
    @13
    @34
    @169
    vh
    @13
    nfcv
    nffv
    #
    nfbr
    vh
    @35
    c1
    cle
    @171
    @170
    vh
    c1
    nfcv
    nfbr
    nfan
    nfral
    @36
    vh
    vt
    @20
    vh
    @20
    nfcv
    vh
    @35
    @17
    clt
    @171
    vh
    clt
    nfcv
    #
    vh
    @17
    nfcv
    nfbr
    nfral
    @38
    vh
    vt
    @54
    vh
    @54
    nfcv
    vh
    @22
    @35
    clt
    vh
    @22
    nfcv
    @172
    @171
    nfbr
    nfral
    nf3an
    @44
    @34
    wceq
    #
    @49
    @166
    @154
    @37
    @55
    @167
    @173
    @48
    @165
    vt
    cT
    vt
    @44
    @34
    vt
    @44
    nfcv
    vt
    @14
    @31
    vt
    @0
    @30
    vt
    @0
    nfcv
    #
    vt
    cG
    @19
    vt
    cG
    @58
    stoweidlem31.6
    vt
    vw
    cR
    @57
    vt
    cR
    nfcv
    @56
    vt
    vh
    cA
    @49
    @52
    @55
    vt
    @48
    vt
    cT
    nfra1
    @50
    vt
    @51
    nfra1
    @53
    vt
    @54
    nfra1
    nf3an
    vt
    cA
    nfcv
    nfrab
    nfmpt
    nfcxfr
    #
    vt
    @19
    nfcv
    nfco
    nfco
    #
    vt
    @14
    nfcv
    nffv
    nfeq
    #
    @173
    @46
    @163
    @47
    @164
    @173
    @45
    @35
    cc0
    cle
    @13
    @44
    @34
    fveq1
    #
    breq2d
    @173
    @45
    @35
    c1
    cle
    @178
    breq1d
    anbi12d
    ralbid
    @173
    @50
    @36
    vt
    @20
    @177
    @173
    @45
    @35
    @17
    clt
    @178
    breq1d
    ralbid
    @173
    @53
    @38
    vt
    @54
    @177
    @173
    @45
    @35
    @22
    clt
    @178
    breq2d
    ralbid
    3anbi123d
    elrabf
    simprbi
    #
    simp2d
    syl6bi
    mpd
    @145
    @38
    vt
    cB
    @29
    @144
    vt
    wph
    @9
    vt
    stoweidlem31.2
    @2
    @8
    vt
    vt
    @1
    @0
    @174
    vt
    cG
    @175
    nfrn
    #
    nffn
    @7
    vt
    vb
    @1
    @180
    @7
    vt
    nfv
    nfral
    nfan
    nfan
    @144
    vt
    nfv
    nfan
    @145
    @13
    cB
    wcel
    #
    @38
    @145
    @181
    @13
    @54
    wcel
    @38
    @145
    @181
    wa
    cB
    @54
    @13
    wph
    cB
    @54
    wss
    @9
    @144
    @181
    stoweidlem31.11
    ad3antrrr
    @145
    @181
    simpr
    sseldd
    @145
    @38
    vt
    @54
    @145
    @147
    @167
    @153
    @145
    @147
    @157
    @167
    @162
    @157
    @166
    @37
    @167
    @179
    simp3d
    syl6bi
    mpd
    r19.21bi
    syldan
    ex
    ralrimi
    jca
    ralrimiva
    jca
    @27
    @42
    vx
    @31
    cvv
    @11
    @31
    wceq
    #
    @12
    @33
    @26
    @41
    @10
    cY
    @11
    @31
    feq1
    @182
    @25
    @40
    vi
    @10
    @182
    @21
    @37
    @24
    @39
    @182
    @18
    @36
    vt
    @20
    vt
    @11
    @31
    vt
    @11
    nfcv
    @176
    nfeq
    #
    @182
    @16
    @35
    @17
    clt
    @182
    @13
    @15
    @34
    @14
    @11
    @31
    fveq1
    fveq1d
    #
    breq1d
    ralbid
    @182
    @23
    @38
    vt
    cB
    @183
    @182
    @16
    @35
    @22
    clt
    @184
    breq2d
    ralbid
    anbi12d
    ralbidv
    anbi12d
    spcegv
    sylc
    exlimddv
end
