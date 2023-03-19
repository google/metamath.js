include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfv.mm"
include "wne.mm"
include "wa.mm"
include "cfz.mm"
include "wrex.mm"
include "wrmo.mm"
include "wn.mm"
include "wcel.mm"
include "caddc.mm"
include "wf1o.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "cuz.mm"
include "wss.mm"
include "cc.mm"
include "wceq.mm"
include "nncnd.mm"
include "npcan1.mm"
include "cz.mm"
include "nnzd.mm"
include "peano2zm.mm"
include "uzid.mm"
include "peano2uz.mm"
include "4syl.mm"
include "eqeltrrd.mm"
include "fzss2.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "fzp1elp1.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "cpr.mm"
include "wral.mm"
include "cima.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "3syl.mm"
include "syl5ss.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "zred.mm"
include "ltp1d.mm"
include "ltned.mm"
include "syldan.mm"
include "csn.mm"
include "cxp.mm"
include "cc0.mm"
include "cun.mm"
include "cof.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "csb.mm"
include "cvv.mm"
include "breq1.mm"
include "id.mm"
include "ifbieq1d.mm"
include "elfzelz.mm"
include "ltm1d.mm"
include "iftrued.mm"
include "sylan9eqr.mm"
include "csbeq1d.mm"
include "wb.mm"
include "elfzm1b.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "xpeq1d.mm"
include "adantl.mm"
include "oveq1.mm"
include "zcnd.mm"
include "oveq1d.mm"
include "uneq12d.mm"
include "csbied.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "fveq1d.mm"
include "wfn.mm"
include "ffn.mm"
include "cin.mm"
include "c0.mm"
include "1ex.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "c0ex.mm"
include "pm3.2i.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "imain.mm"
include "fzdisj.mm"
include "ima0.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "fnun.mm"
include "sylancr.mm"
include "elfzuz.mm"
include "eqeltrd.mm"
include "uzss.mm"
include "elfzuz3.mm"
include "eluzp1p1.mm"
include "fzsplit2.mm"
include "uneq2d.mm"
include "imaundi.mm"
include "f1ofo.mm"
include "foima.mm"
include "fneq2d.mm"
include "inidm.mm"
include "eqidd.mm"
include "imass2.mm"
include "fvun2.mm"
include "mp3an12.mm"
include "fvconst2.mm"
include "ofval.mm"
include "mpdan.mm"
include "addid1d.mm"
include "3eqtrd.mm"
include "ifbieq2d.mm"
include "ltnrd.mm"
include "iffalsed.mm"
include "ovex.mm"
include "csbie.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "sseldi.mm"
include "cr.mm"
include "peano2re.mm"
include "fzsplit.mm"
include "fvun1.mm"
include "3netr4d.mm"
include "ralrimiva.mm"
include "fzpr.mm"
include "f1ofn.mm"
include "fnimapr.mm"
include "syl3anc.mm"
include "raleqdv.mm"
include "fvex.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "ralpr.mm"
include "sylib.mm"
include "wf1.mm"
include "wi.mm"
include "f1of1.mm"
include "f1veqaeq.mm"
include "syl12anc.mm"
include "necon3d.mm"
include "mpd.mm"
include "anbi1d.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "neeq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "dfrex2.mm"
include "weq.mm"
include "rmo4.mm"
include "dfral2.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "annim.mm"
include "bitri.mm"
include "rexbii.mm"
include "xchbinxr.mm"
include "ralbii.mm"

theorem poimirlem1
  let wph: wff ph
  let vy: setvar y
  let cT: class T
  let cU: class U
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cV: class V
  assume poimir.0: |- ( ph -> N e. NN )
  assume poimirlem2.1: |- ( ph -> F = ( y e. ( 0 ... ( N - 1 ) ) |-> [_ if ( y < M , y , ( y + 1 ) ) / j ]_ ( T oF + ( ( ( U " ( 1 ... j ) ) X. { 1 } ) u. ( ( U " ( ( j + 1 ) ... N ) ) X. { 0 } ) ) ) ) )
  assume poimirlem2.2: |- ( ph -> T : ( 1 ... N ) --> ZZ )
  assume poimirlem2.3: |- ( ph -> U : ( 1 ... N ) -1-1-onto-> ( 1 ... N ) )
  assume poimirlem1.4: |- ( ph -> M e. ( 1 ... ( N - 1 ) ) )

  disjoint j n
  disjoint j y
  disjoint n y
  disjoint j ph
  disjoint n ph
  disjoint ph y
  disjoint F j
  disjoint F n
  disjoint F y
  disjoint M j
  disjoint M n
  disjoint M y
  disjoint N j
  disjoint N n
  disjoint N y
  disjoint T j
  disjoint T n
  disjoint T y
  disjoint U j
  disjoint U n
  disjoint U y
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint i q
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint j k
  disjoint j m
  disjoint j p
  disjoint j q
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j w
  disjoint j x
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint p q
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint m ph
  disjoint F m
  disjoint M m
  disjoint N m
  disjoint T m
  disjoint U m
  disjoint V j
  disjoint V m
  disjoint V n
  disjoint V y
  assert |- ( ph -> -. E* n e. ( 1 ... N ) ( ( F ` ( M - 1 ) ) ` n ) =/= ( ( F ` M ) ` n ) )

  proof
    wph
    vn
    cv
    #
    cM
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cfv
    #
    @0
    cM
    cF
    cfv
    #
    cfv
    #
    wne
    #
    vm
    cv
    #
    @2
    cfv
    #
    @7
    @4
    cfv
    #
    wne
    #
    wa
    #
    @0
    @7
    wne
    #
    wa
    #
    vm
    c1
    cN
    cfz
    co
    #
    wrex
    #
    vn
    @14
    wrex
    #
    @6
    vn
    @14
    wrmo
    #
    wn
    wph
    cM
    cU
    cfv
    #
    @14
    wcel
    cM
    c1
    caddc
    co
    #
    cU
    cfv
    #
    @14
    wcel
    @18
    @2
    cfv
    #
    @18
    @4
    cfv
    #
    wne
    #
    @20
    @2
    cfv
    #
    @20
    @4
    cfv
    #
    wne
    #
    wa
    #
    @18
    @20
    wne
    #
    @16
    wph
    @14
    @14
    cM
    cU
    wph
    @14
    @14
    cU
    wf1o
    #
    @14
    @14
    cU
    wf
    #
    poimirlem2.3
    @14
    @14
    cU
    f1of
    #
    syl
    #
    wph
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @14
    cM
    wph
    cN
    @33
    cuz
    cfv
    #
    wcel
    @34
    @14
    wss
    wph
    @33
    c1
    caddc
    co
    #
    cN
    @35
    wph
    cN
    cc
    wcel
    @36
    cN
    wceq
    wph
    cN
    poimir.0
    nncnd
    cN
    npcan1
    syl
    #
    wph
    cN
    cz
    wcel
    #
    @33
    cz
    wcel
    #
    @33
    @35
    wcel
    @36
    @35
    wcel
    wph
    cN
    poimir.0
    nnzd
    #
    cN
    peano2zm
    #
    @33
    uzid
    @33
    @33
    peano2uz
    4syl
    eqeltrrd
    @33
    c1
    cN
    fzss2
    syl
    poimirlem1.4
    sseldd
    #
    ffvelrnd
    wph
    @14
    @14
    @19
    cU
    @32
    wph
    @19
    c1
    @36
    cfz
    co
    #
    @14
    wph
    cM
    @34
    wcel
    #
    @19
    @43
    wcel
    poimirlem1.4
    cM
    c1
    @33
    fzp1elp1
    syl
    wph
    @36
    cN
    c1
    cfz
    @37
    oveq2d
    eleqtrd
    #
    ffvelrnd
    wph
    @6
    vn
    @18
    @20
    cpr
    #
    wral
    #
    @27
    wph
    @6
    vn
    cU
    cM
    @19
    cfz
    co
    #
    cima
    #
    wral
    @47
    wph
    @6
    vn
    @49
    wph
    @0
    @49
    wcel
    #
    wa
    #
    @0
    cT
    cfv
    #
    @52
    c1
    caddc
    co
    #
    @3
    @5
    wph
    @50
    @0
    @14
    wcel
    #
    @52
    @53
    wne
    wph
    @49
    @14
    @0
    wph
    @49
    cU
    crn
    #
    @14
    cU
    @48
    imassrn
    wph
    @29
    @30
    @55
    @14
    wss
    poimirlem2.3
    @31
    @14
    @14
    cU
    frn
    3syl
    syl5ss
    sselda
    #
    wph
    @54
    wa
    #
    @52
    @53
    @57
    @52
    wph
    @14
    cz
    @0
    cT
    poimirlem2.2
    ffvelrnda
    #
    zred
    #
    @57
    @52
    @59
    ltp1d
    ltned
    syldan
    @51
    @3
    @0
    cT
    cU
    c1
    @1
    cfz
    co
    #
    cima
    #
    c1
    csn
    #
    cxp
    #
    cU
    cM
    cN
    cfz
    co
    #
    cima
    #
    cc0
    csn
    #
    cxp
    #
    cun
    #
    caddc
    cof
    #
    co
    #
    cfv
    #
    @52
    cc0
    caddc
    co
    #
    @52
    wph
    @3
    @71
    wceq
    @50
    wph
    @0
    @2
    @70
    wph
    vy
    @1
    vj
    vy
    cv
    #
    cM
    clt
    wbr
    #
    @73
    @73
    c1
    caddc
    co
    #
    cif
    #
    cT
    cU
    c1
    vj
    cv
    #
    cfz
    co
    #
    cima
    #
    @62
    cxp
    #
    cU
    @77
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cima
    #
    @66
    cxp
    #
    cun
    #
    @69
    co
    #
    csb
    #
    @70
    cc0
    @33
    cfz
    co
    #
    cF
    cvv
    poimirlem2.1
    wph
    @73
    @1
    wceq
    #
    wa
    #
    @87
    vj
    @1
    @86
    csb
    #
    @70
    @90
    vj
    @76
    @1
    @86
    @89
    wph
    @76
    @1
    cM
    clt
    wbr
    #
    @1
    @75
    cif
    @1
    @89
    @74
    @92
    @73
    @1
    @75
    @73
    @1
    cM
    clt
    breq1
    @89
    id
    ifbieq1d
    wph
    @92
    @1
    @75
    wph
    cM
    wph
    cM
    wph
    @44
    cM
    cz
    wcel
    #
    poimirlem1.4
    cM
    c1
    @33
    elfzelz
    #
    syl
    #
    zred
    #
    ltm1d
    #
    iftrued
    sylan9eqr
    csbeq1d
    wph
    @91
    @70
    wceq
    @89
    wph
    vj
    @1
    @86
    @70
    cc0
    @33
    c1
    cmin
    co
    #
    cfz
    co
    #
    wph
    @44
    @1
    @99
    wcel
    #
    poimirlem1.4
    wph
    @93
    @39
    @44
    @100
    wb
    @95
    wph
    @38
    @39
    @40
    @41
    syl
    #
    cM
    @33
    elfzm1b
    syl2anc
    mpbid
    #
    wph
    @77
    @1
    wceq
    #
    wa
    #
    @85
    @68
    cT
    @69
    @104
    @80
    @63
    @84
    @67
    @103
    @80
    @63
    wceq
    wph
    @103
    @79
    @61
    @62
    @103
    @78
    @60
    cU
    @77
    @1
    c1
    cfz
    oveq2
    imaeq2d
    xpeq1d
    adantl
    @104
    @83
    @65
    @66
    @104
    @82
    @64
    cU
    @104
    @81
    cM
    cN
    cfz
    @103
    wph
    @81
    @1
    c1
    caddc
    co
    #
    cM
    @77
    @1
    c1
    caddc
    oveq1
    wph
    cM
    cc
    wcel
    @105
    cM
    wceq
    wph
    cM
    @95
    zcnd
    cM
    npcan1
    syl
    #
    sylan9eqr
    oveq1d
    imaeq2d
    xpeq1d
    uneq12d
    oveq2d
    csbied
    adantr
    eqtrd
    wph
    @99
    @88
    @1
    wph
    @33
    @98
    cuz
    cfv
    #
    wcel
    @99
    @88
    wss
    wph
    @98
    c1
    caddc
    co
    #
    @33
    @107
    wph
    @33
    cc
    wcel
    @108
    @33
    wceq
    wph
    @33
    @101
    zcnd
    @33
    npcan1
    syl
    wph
    @39
    @98
    cz
    wcel
    @98
    @107
    wcel
    @108
    @107
    wcel
    @101
    @33
    peano2zm
    @98
    uzid
    @98
    @98
    peano2uz
    4syl
    eqeltrrd
    @98
    cc0
    @33
    fzss2
    syl
    @102
    sseldd
    wph
    cT
    @68
    @69
    ovexd
    fvmptd
    fveq1d
    adantr
    @51
    @54
    @71
    @72
    wceq
    @56
    @51
    @14
    @14
    @52
    cc0
    caddc
    @14
    cT
    @68
    cvv
    cvv
    @0
    wph
    cT
    @14
    wfn
    #
    @50
    wph
    @14
    cz
    cT
    wf
    @109
    poimirlem2.2
    @14
    cz
    cT
    ffn
    syl
    adantr
    #
    wph
    @68
    @14
    wfn
    #
    @50
    wph
    @68
    @61
    @65
    cun
    #
    wfn
    #
    @111
    wph
    @63
    @61
    wfn
    #
    @67
    @65
    wfn
    #
    wa
    @61
    @65
    cin
    #
    c0
    wceq
    #
    @113
    @114
    @115
    c1
    cvv
    wcel
    #
    @114
    1ex
    @61
    c1
    cvv
    fnconstg
    ax-mp
    #
    cc0
    cvv
    wcel
    #
    @115
    c0ex
    @65
    cc0
    cvv
    fnconstg
    ax-mp
    #
    pm3.2i
    wph
    cU
    @60
    @64
    cin
    #
    cima
    #
    @116
    c0
    wph
    @29
    cU
    ccnv
    wfun
    #
    @123
    @116
    wceq
    poimirlem2.3
    @29
    @14
    @14
    cU
    wfo
    #
    @124
    @14
    @14
    cU
    dff1o3
    simprbi
    #
    @60
    @64
    cU
    imain
    3syl
    wph
    @123
    cU
    c0
    cima
    #
    c0
    wph
    @122
    c0
    cU
    wph
    @92
    @122
    c0
    wceq
    @97
    c1
    @1
    cM
    cN
    fzdisj
    syl
    imaeq2d
    cU
    ima0
    #
    syl6eq
    eqtr3d
    #
    @61
    @65
    @63
    @67
    fnun
    sylancr
    wph
    @112
    @14
    @68
    wph
    cU
    @14
    cima
    #
    @112
    @14
    wph
    @130
    cU
    @60
    @64
    cun
    #
    cima
    @112
    wph
    @14
    @131
    cU
    wph
    @14
    @60
    @105
    cN
    cfz
    co
    #
    cun
    #
    @131
    wph
    @105
    c1
    cuz
    cfv
    #
    wcel
    cN
    @1
    cuz
    cfv
    #
    wcel
    @14
    @133
    wceq
    wph
    @105
    cM
    @134
    @106
    wph
    @44
    cM
    @134
    wcel
    #
    poimirlem1.4
    cM
    c1
    @33
    elfzuz
    syl
    #
    eqeltrd
    wph
    @19
    cuz
    cfv
    #
    @135
    cN
    wph
    cM
    @135
    wcel
    @19
    @135
    wcel
    @138
    @135
    wss
    wph
    @105
    cM
    @135
    @106
    wph
    @93
    @1
    cz
    wcel
    @1
    @135
    wcel
    @105
    @135
    wcel
    @95
    cM
    peano2zm
    @1
    uzid
    @1
    @1
    peano2uz
    4syl
    eqeltrrd
    @1
    cM
    peano2uz
    @1
    @19
    uzss
    3syl
    wph
    @36
    cN
    @138
    @37
    wph
    @44
    @33
    cM
    cuz
    cfv
    wcel
    @36
    @138
    wcel
    poimirlem1.4
    cM
    c1
    @33
    elfzuz3
    cM
    @33
    eluzp1p1
    3syl
    eqeltrrd
    #
    sseldd
    @1
    c1
    cN
    fzsplit2
    syl2anc
    wph
    @132
    @64
    @60
    wph
    @105
    cM
    cN
    cfz
    @106
    oveq1d
    uneq2d
    eqtrd
    imaeq2d
    cU
    @60
    @64
    imaundi
    syl6eq
    wph
    @29
    @125
    @130
    @14
    wceq
    poimirlem2.3
    @14
    @14
    cU
    f1ofo
    @14
    @14
    cU
    foima
    3syl
    #
    eqtr3d
    fneq2d
    mpbid
    adantr
    @51
    c1
    cN
    cfz
    ovexd
    #
    @141
    @14
    inidm
    #
    @51
    @54
    wa
    @52
    eqidd
    #
    @51
    @0
    @68
    cfv
    #
    cc0
    wceq
    @54
    @51
    @144
    @0
    @67
    cfv
    #
    cc0
    @51
    @117
    @0
    @65
    wcel
    #
    @144
    @145
    wceq
    #
    wph
    @117
    @50
    @129
    adantr
    wph
    @49
    @65
    @0
    wph
    cN
    @138
    wcel
    @48
    @64
    wss
    @49
    @65
    wss
    @139
    @19
    cM
    cN
    fzss2
    @48
    @64
    cU
    imass2
    3syl
    sselda
    #
    @114
    @115
    @117
    @146
    wa
    @147
    @119
    @121
    @61
    @65
    @63
    @67
    @0
    fvun2
    mp3an12
    syl2anc
    @51
    @146
    @145
    cc0
    wceq
    @148
    @65
    cc0
    @0
    c0ex
    fvconst2
    syl
    eqtrd
    adantr
    ofval
    mpdan
    wph
    @50
    @54
    @72
    @52
    wceq
    @56
    @57
    @52
    @57
    @52
    @58
    zcnd
    addid1d
    syldan
    3eqtrd
    @51
    @5
    @0
    cT
    cU
    c1
    @19
    cfz
    co
    #
    cima
    #
    @62
    cxp
    #
    cU
    @19
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cima
    #
    @66
    cxp
    #
    cun
    #
    @69
    co
    #
    cfv
    #
    @53
    wph
    @5
    @158
    wceq
    @50
    wph
    @0
    @4
    @157
    wph
    vy
    cM
    @87
    @157
    @88
    cF
    cvv
    poimirlem2.1
    wph
    @73
    cM
    wceq
    #
    wa
    #
    @87
    vj
    @19
    @86
    csb
    @157
    @160
    vj
    @76
    @19
    @86
    @159
    wph
    @76
    cM
    cM
    clt
    wbr
    #
    @73
    @19
    cif
    @19
    @159
    @74
    @161
    @75
    @19
    @73
    @73
    cM
    cM
    clt
    breq1
    @73
    cM
    c1
    caddc
    oveq1
    ifbieq2d
    wph
    @161
    @73
    @19
    wph
    cM
    @96
    ltnrd
    iffalsed
    sylan9eqr
    csbeq1d
    vj
    @19
    @86
    @157
    cM
    c1
    caddc
    ovex
    @77
    @19
    wceq
    #
    @85
    @156
    cT
    @69
    @162
    @80
    @151
    @84
    @155
    @162
    @79
    @150
    @62
    @162
    @78
    @149
    cU
    @77
    @19
    c1
    cfz
    oveq2
    imaeq2d
    xpeq1d
    @162
    @83
    @154
    @66
    @162
    @82
    @153
    cU
    @162
    @81
    @152
    cN
    cfz
    @77
    @19
    c1
    caddc
    oveq1
    oveq1d
    imaeq2d
    xpeq1d
    uneq12d
    oveq2d
    csbie
    syl6eq
    wph
    @34
    @88
    cM
    c1
    cc0
    cuz
    cfv
    wcel
    @34
    @88
    wss
    1eluzge0
    c1
    cc0
    @33
    fzss1
    ax-mp
    poimirlem1.4
    sseldi
    wph
    cT
    @156
    @69
    ovexd
    fvmptd
    fveq1d
    adantr
    @51
    @54
    @158
    @53
    wceq
    @56
    @51
    @14
    @14
    @52
    c1
    caddc
    @14
    cT
    @156
    cvv
    cvv
    @0
    @110
    wph
    @156
    @14
    wfn
    #
    @50
    wph
    @156
    @150
    @154
    cun
    #
    wfn
    #
    @163
    wph
    @151
    @150
    wfn
    #
    @155
    @154
    wfn
    #
    wa
    @150
    @154
    cin
    #
    c0
    wceq
    #
    @165
    @166
    @167
    @118
    @166
    1ex
    @150
    c1
    cvv
    fnconstg
    ax-mp
    #
    @120
    @167
    c0ex
    @154
    cc0
    cvv
    fnconstg
    ax-mp
    #
    pm3.2i
    wph
    @168
    @127
    c0
    wph
    cU
    @149
    @153
    cin
    #
    cima
    #
    @168
    @127
    wph
    @29
    @124
    @173
    @168
    wceq
    poimirlem2.3
    @126
    @149
    @153
    cU
    imain
    3syl
    wph
    @172
    c0
    cU
    wph
    @19
    @152
    clt
    wbr
    @172
    c0
    wceq
    wph
    @19
    wph
    cM
    cr
    wcel
    @19
    cr
    wcel
    @96
    cM
    peano2re
    syl
    ltp1d
    c1
    @19
    @152
    cN
    fzdisj
    syl
    imaeq2d
    eqtr3d
    @128
    syl6eq
    #
    @150
    @154
    @151
    @155
    fnun
    sylancr
    wph
    @164
    @14
    @156
    wph
    @130
    @164
    @14
    wph
    @130
    cU
    @149
    @153
    cun
    #
    cima
    @164
    wph
    @14
    @175
    cU
    wph
    @19
    @14
    wcel
    #
    @14
    @175
    wceq
    @45
    @19
    c1
    cN
    fzsplit
    syl
    imaeq2d
    cU
    @149
    @153
    imaundi
    syl6eq
    @140
    eqtr3d
    fneq2d
    mpbid
    adantr
    @141
    @141
    @142
    @143
    @51
    @0
    @156
    cfv
    #
    c1
    wceq
    @54
    @51
    @177
    @0
    @151
    cfv
    #
    c1
    @51
    @169
    @0
    @150
    wcel
    #
    @177
    @178
    wceq
    #
    wph
    @169
    @50
    @174
    adantr
    wph
    @49
    @150
    @0
    wph
    @136
    @48
    @149
    wss
    @49
    @150
    wss
    @137
    cM
    c1
    @19
    fzss1
    @48
    @149
    cU
    imass2
    3syl
    sselda
    #
    @166
    @167
    @169
    @179
    wa
    @180
    @170
    @171
    @150
    @154
    @151
    @155
    @0
    fvun1
    mp3an12
    syl2anc
    @51
    @179
    @178
    c1
    wceq
    @181
    @150
    c1
    @0
    1ex
    fvconst2
    syl
    eqtrd
    adantr
    ofval
    mpdan
    eqtrd
    3netr4d
    ralrimiva
    wph
    @6
    vn
    @49
    @46
    wph
    @49
    cU
    cM
    @19
    cpr
    #
    cima
    #
    @46
    wph
    @48
    @182
    cU
    wph
    @44
    @93
    @48
    @182
    wceq
    poimirlem1.4
    @94
    cM
    fzpr
    3syl
    imaeq2d
    wph
    cU
    @14
    wfn
    #
    cM
    @14
    wcel
    #
    @176
    @183
    @46
    wceq
    wph
    @29
    @184
    poimirlem2.3
    @14
    @14
    cU
    f1ofn
    syl
    @42
    @45
    @14
    cM
    @19
    cU
    fnimapr
    syl3anc
    eqtrd
    raleqdv
    mpbid
    @6
    @23
    @26
    vn
    @18
    @20
    cM
    cU
    fvex
    @19
    cU
    fvex
    @0
    @18
    wceq
    #
    @3
    @21
    @5
    @22
    @0
    @18
    @2
    fveq2
    @0
    @18
    @4
    fveq2
    neeq12d
    #
    @0
    @20
    wceq
    @3
    @24
    @5
    @25
    @0
    @20
    @2
    fveq2
    @0
    @20
    @4
    fveq2
    neeq12d
    ralpr
    sylib
    wph
    cM
    @19
    wne
    @28
    wph
    cM
    @19
    @96
    wph
    cM
    @96
    ltp1d
    ltned
    wph
    @18
    @20
    cM
    @19
    wph
    @14
    @14
    cU
    wf1
    #
    @185
    @176
    @18
    @20
    wceq
    cM
    @19
    wceq
    wi
    wph
    @29
    @188
    poimirlem2.3
    @14
    @14
    cU
    f1of1
    syl
    @42
    @45
    @14
    @14
    cM
    @19
    cU
    f1veqaeq
    syl12anc
    necon3d
    mpd
    @13
    @27
    @28
    wa
    @23
    @10
    wa
    #
    @18
    @7
    wne
    #
    wa
    vn
    vm
    @18
    @20
    @14
    @14
    @186
    @11
    @189
    @12
    @190
    @186
    @6
    @23
    @10
    @187
    anbi1d
    @0
    @18
    @7
    neeq1
    anbi12d
    @7
    @20
    wceq
    #
    @189
    @27
    @190
    @28
    @191
    @10
    @26
    @23
    @191
    @8
    @24
    @9
    @25
    @7
    @20
    @2
    fveq2
    @7
    @20
    @4
    fveq2
    neeq12d
    anbi2d
    @7
    @20
    @18
    neeq2
    anbi12d
    rspc2ev
    syl112anc
    @16
    @15
    wn
    #
    vn
    @14
    wral
    #
    @17
    @15
    vn
    @14
    dfrex2
    @17
    @11
    vn
    vm
    weq
    #
    wi
    #
    vm
    @14
    wral
    #
    vn
    @14
    wral
    @193
    @6
    @10
    vn
    vm
    @14
    @194
    @3
    @8
    @5
    @9
    @0
    @7
    @2
    fveq2
    @0
    @7
    @4
    fveq2
    neeq12d
    rmo4
    @196
    @192
    vn
    @14
    @196
    @195
    wn
    #
    vm
    @14
    wrex
    @15
    @195
    vm
    @14
    dfral2
    @13
    @197
    vm
    @14
    @13
    @11
    @194
    wn
    #
    wa
    @197
    @12
    @198
    @11
    @0
    @7
    df-ne
    anbi2i
    @11
    @194
    annim
    bitri
    rexbii
    xchbinxr
    ralbii
    bitri
    xchbinxr
    sylib
end
