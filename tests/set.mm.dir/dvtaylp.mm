include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "cdv.mm"
include "ctayl.mm"
include "wceq.mm"
include "cif.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "ctopon.mm"
include "toponmax.mm"
include "mp1i.mm"
include "fzfid.mm"
include "w3a.mm"
include "wa.mm"
include "cdm.mm"
include "cpm.mm"
include "cn0.mm"
include "wf.mm"
include "adantr.mm"
include "wss.mm"
include "cnex.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "elfznn0.mm"
include "adantl.mm"
include "dvnf.mm"
include "syl3anc.mm"
include "cicc.mm"
include "cz.mm"
include "cin.mm"
include "0z.mm"
include "peano2nn0.mm"
include "syl.mm"
include "nn0zd.mm"
include "fzval2.mm"
include "sylancr.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "taylplem1.mm"
include "syldan.mm"
include "ffvelrnd.mm"
include "cn.mm"
include "faccl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "3adant3.mm"
include "simp3.mm"
include "recnprss.mm"
include "sstrd.mm"
include "dvnbss.mm"
include "fdm.mm"
include "sseqtrd.mm"
include "sseldd.mm"
include "3ad2ant1.mm"
include "subcld.mm"
include "3ad2ant2.mm"
include "expcld.mm"
include "mulcld.mm"
include "0cnd.mm"
include "wn.mm"
include "nn0cnd.mm"
include "wne.mm"
include "simpr.mm"
include "neqned.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "nnm1nn0.mm"
include "ifclda.mm"
include "3expa.mm"
include "1cnd.mm"
include "c0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "dvmptid.mm"
include "ad2antrr.mm"
include "dvmptc.mm"
include "dvmptsub.mm"
include "1m0e1.mm"
include "mpteq2i.mm"
include "syl6eq.mm"
include "dvexp2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "ifeq2d.mm"
include "dvmptco.mm"
include "mulid1d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "dvmptcmul.mm"
include "dvmptfsum.mm"
include "1zzd.mm"
include "0zd.mm"
include "dvfg.mm"
include "dvbss.mm"
include "1nn0.mm"
include "dvnadd.mm"
include "dvn1.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "addcomd.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "dmeqd.mm"
include "eleqtrrd.mm"
include "taylplem2.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "fsumshft.mm"
include "elfznn.mm"
include "ifnefalse.mm"
include "simpll.mm"
include "cuz.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "sseli.mm"
include "simplr.mm"
include "mulassd.mm"
include "facp1.mm"
include "npcand.mm"
include "div23d.mm"
include "divcan5rd.mm"
include "pncan3d.mm"
include "3eqtr3rd.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "sumeq2dv.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "sumeq1i.mm"
include "syl6eqr.mm"
include "an32s.mm"
include "sylan2.mm"
include "cdif.mm"
include "eldif.mm"
include "wi.mm"
include "biimpri.mm"
include "sylan.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "elfzuz3.mm"
include "elfzuzb.mm"
include "ex.mm"
include "necon1bd.mm"
include "impr.mm"
include "sylan2b.mm"
include "iftrued.mm"
include "eldifi.mm"
include "adantlr.mm"
include "mul01d.mm"
include "fsumss.mm"
include "3eqtr2rd.mm"
include "taylpfval.mm"
include "3eqtr4d.mm"

theorem dvtaylp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume dvtaylp.s: |- ( ph -> S e. { RR , CC } )
  assume dvtaylp.f: |- ( ph -> F : A --> CC )
  assume dvtaylp.a: |- ( ph -> A C_ S )
  assume dvtaylp.n: |- ( ph -> N e. NN0 )
  assume dvtaylp.b: |- ( ph -> B e. dom ( ( S Dn F ) ` ( N + 1 ) ) )


  assert |- ( ph -> ( CC _D ( ( N + 1 ) ( S Tayl F ) B ) ) = ( N ( S Tayl ( S _D F ) ) B ) )

  proof
    wph
    cc
    vx
    cc
    cc0
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    @2
    cfa
    cfv
    #
    cdiv
    co
    #
    vx
    cv
    #
    cB
    cmin
    co
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    cmpt
    #
    cdv
    co
    #
    vx
    cc
    cc0
    cN
    cfz
    co
    cB
    vj
    cv
    #
    cS
    cS
    cF
    cdv
    co
    #
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    @14
    cfa
    cfv
    #
    cdiv
    co
    #
    @9
    @14
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    cc
    @0
    cB
    cS
    cF
    ctayl
    co
    co
    #
    cdv
    co
    cN
    cB
    cS
    @15
    ctayl
    co
    co
    #
    wph
    @13
    vx
    cc
    @1
    @7
    @2
    cc0
    wceq
    #
    cc0
    @2
    @9
    @2
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    @24
    wph
    vx
    @11
    @32
    cc
    vk
    @1
    ccnfld
    ctopn
    cfv
    #
    @34
    cc
    @34
    cc
    crest
    co
    #
    @34
    @34
    cvv
    wcel
    @35
    @34
    wceq
    ccnfld
    ctopn
    fvex
    @34
    cvv
    cc
    cc
    @34
    @34
    @34
    eqid
    #
    cnfldtopon
    #
    toponunii
    restid
    ax-mp
    eqcomi
    @36
    cc
    cr
    cc
    cpr
    #
    wcel
    #
    wph
    cnelprrecn
    a1i
    @34
    cc
    ctopon
    cfv
    wcel
    cc
    @34
    wcel
    wph
    @37
    cc
    @34
    toponmax
    mp1i
    wph
    cc0
    @0
    fzfid
    wph
    @2
    @1
    wcel
    #
    @8
    cc
    wcel
    #
    w3a
    #
    @7
    @10
    wph
    @40
    @7
    cc
    wcel
    #
    @41
    wph
    @40
    wa
    #
    @5
    @6
    @44
    @4
    cdm
    #
    cc
    cB
    @4
    @44
    cS
    @38
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    @2
    cn0
    wcel
    #
    @45
    cc
    @4
    wf
    wph
    @46
    @40
    dvtaylp.s
    adantr
    wph
    @47
    @40
    wph
    cc
    cvv
    wcel
    #
    @46
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    @47
    @49
    wph
    cnex
    a1i
    dvtaylp.s
    dvtaylp.f
    dvtaylp.a
    cc
    cS
    cA
    cF
    cvv
    @38
    elpm2r
    syl22anc
    #
    adantr
    @40
    @48
    wph
    @2
    @0
    elfznn0
    #
    adantl
    #
    cS
    cF
    @2
    dvnf
    syl3anc
    wph
    @40
    @2
    cc0
    @0
    cicc
    co
    cz
    cin
    #
    wcel
    #
    cB
    @45
    wcel
    wph
    @40
    @55
    wph
    @1
    @54
    @2
    wph
    cc0
    cz
    wcel
    @0
    cz
    wcel
    @1
    @54
    wceq
    0z
    wph
    @0
    wph
    cN
    cn0
    wcel
    #
    @0
    cn0
    wcel
    #
    dvtaylp.n
    cN
    peano2nn0
    syl
    #
    nn0zd
    cc0
    @0
    fzval2
    sylancr
    eleq2d
    biimpa
    wph
    cA
    cB
    cS
    vk
    cF
    @0
    dvtaylp.s
    dvtaylp.f
    dvtaylp.a
    @58
    dvtaylp.b
    taylplem1
    syldan
    ffvelrnd
    #
    @44
    @6
    @44
    @48
    @6
    cn
    wcel
    @53
    @2
    faccl
    syl
    #
    nncnd
    #
    @44
    @6
    @60
    nnne0d
    #
    divcld
    #
    3adant3
    #
    @42
    @9
    @2
    @42
    @8
    cB
    wph
    @40
    @41
    simp3
    wph
    @40
    cB
    cc
    wcel
    #
    @41
    wph
    cA
    cc
    cB
    wph
    cA
    cS
    cc
    dvtaylp.a
    wph
    @46
    cS
    cc
    wss
    #
    dvtaylp.s
    cS
    recnprss
    syl
    #
    sstrd
    wph
    @0
    @3
    cfv
    #
    cdm
    #
    cA
    cB
    wph
    @69
    cF
    cdm
    #
    cA
    wph
    @46
    @47
    @57
    @69
    @70
    wss
    dvtaylp.s
    @51
    @58
    cS
    cF
    @0
    dvnbss
    syl3anc
    wph
    @50
    @70
    cA
    wceq
    dvtaylp.f
    cA
    cc
    cF
    fdm
    syl
    sseqtrd
    dvtaylp.b
    sseldd
    sseldd
    #
    3ad2ant1
    subcld
    #
    @40
    wph
    @48
    @41
    @52
    3ad2ant2
    #
    expcld
    #
    mulcld
    @42
    @7
    @31
    @64
    @42
    @27
    cc0
    @30
    cc
    @42
    @27
    wa
    0cnd
    @42
    @27
    wn
    #
    wa
    #
    @2
    @29
    @42
    @2
    cc
    wcel
    @75
    @42
    @2
    @73
    nn0cnd
    adantr
    @76
    @9
    @28
    @42
    @9
    cc
    wcel
    #
    @75
    @72
    adantr
    @76
    @2
    cn
    wcel
    #
    @28
    cn0
    wcel
    #
    @76
    @48
    @2
    cc0
    wne
    #
    @78
    @42
    @48
    @75
    @73
    adantr
    @76
    @2
    cc0
    @42
    @75
    simpr
    neqned
    @2
    elnnne0
    #
    sylanbrc
    @2
    nnm1nn0
    #
    syl
    expcld
    mulcld
    ifclda
    #
    mulcld
    @44
    vx
    @10
    @31
    @7
    cc
    cc
    cc
    @39
    @44
    cnelprrecn
    a1i
    #
    wph
    @40
    @41
    @10
    cc
    wcel
    @74
    3expa
    wph
    @40
    @41
    @31
    cc
    wcel
    #
    @83
    3expa
    #
    @44
    cc
    vx
    cc
    @10
    cmpt
    cdv
    co
    vx
    cc
    @31
    c1
    cmul
    co
    #
    cmpt
    vx
    cc
    @31
    cmpt
    @44
    vx
    vy
    @9
    c1
    vy
    cv
    #
    @2
    cexp
    co
    #
    @27
    cc0
    @2
    @88
    @28
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cc
    cc
    @10
    @31
    cc
    cvv
    cc
    cc
    @84
    @84
    wph
    @40
    @41
    @77
    @72
    3expa
    @44
    @41
    wa
    #
    1cnd
    #
    @44
    @88
    cc
    wcel
    #
    wa
    #
    @88
    @2
    @44
    @95
    simpr
    @44
    @48
    @95
    @53
    adantr
    expcld
    @92
    cvv
    wcel
    @96
    @27
    cc0
    @91
    c0ex
    @2
    @90
    cmul
    ovex
    ifex
    a1i
    @44
    cc
    vx
    cc
    @9
    cmpt
    cdv
    co
    vx
    cc
    c1
    cc0
    cmin
    co
    #
    cmpt
    vx
    cc
    c1
    cmpt
    @44
    vx
    @8
    c1
    cB
    cc0
    cc
    cc
    cc
    cc
    @84
    @44
    @41
    simpr
    @94
    @44
    vx
    cc
    @84
    dvmptid
    wph
    @65
    @40
    @41
    @71
    ad2antrr
    @93
    0cnd
    @44
    vx
    cB
    cc
    @84
    wph
    @65
    @40
    @71
    adantr
    dvmptc
    dvmptsub
    vx
    cc
    @97
    c1
    1m0e1
    mpteq2i
    syl6eq
    @44
    @48
    cc
    vy
    cc
    @89
    cmpt
    cdv
    co
    vy
    cc
    @92
    cmpt
    wceq
    @53
    vy
    @2
    dvexp2
    syl
    @88
    @9
    @2
    cexp
    oveq1
    @88
    @9
    wceq
    #
    @27
    @91
    @30
    cc0
    @98
    @90
    @29
    @2
    cmul
    @88
    @9
    @28
    cexp
    oveq1
    oveq2d
    ifeq2d
    dvmptco
    @44
    vx
    cc
    @87
    @31
    @93
    @31
    @86
    mulid1d
    mpteq2dva
    eqtrd
    @63
    dvmptcmul
    dvmptfsum
    wph
    vx
    cc
    @33
    @23
    wph
    @41
    wa
    #
    @23
    cc0
    c1
    caddc
    co
    #
    @0
    cfz
    co
    #
    cB
    @28
    @16
    cfv
    #
    cfv
    #
    @28
    cfa
    cfv
    #
    cdiv
    co
    #
    @29
    cmul
    co
    #
    vk
    csu
    #
    c1
    @0
    cfz
    co
    #
    @32
    vk
    csu
    #
    @33
    @99
    @22
    @106
    vj
    vk
    c1
    cc0
    cN
    @99
    1zzd
    @99
    0zd
    wph
    cN
    cz
    wcel
    @41
    wph
    cN
    dvtaylp.n
    nn0zd
    adantr
    wph
    @15
    cdm
    #
    cB
    cS
    vj
    @15
    cN
    @8
    dvtaylp.s
    wph
    @46
    @110
    cc
    @15
    wf
    dvtaylp.s
    cS
    cF
    dvfg
    syl
    #
    wph
    @110
    cA
    cS
    wph
    cA
    cS
    cF
    @67
    dvtaylp.f
    dvtaylp.a
    dvbss
    dvtaylp.a
    sstrd
    #
    dvtaylp.n
    wph
    cB
    @69
    cN
    @16
    cfv
    #
    cdm
    dvtaylp.b
    wph
    @113
    @68
    wph
    cN
    cS
    c1
    @3
    cfv
    #
    cdvn
    co
    #
    cfv
    #
    c1
    cN
    caddc
    co
    #
    @3
    cfv
    #
    @113
    @68
    wph
    @46
    @47
    c1
    cn0
    wcel
    #
    @56
    @116
    @118
    wceq
    dvtaylp.s
    @51
    @119
    wph
    1nn0
    a1i
    dvtaylp.n
    cS
    cF
    c1
    cN
    dvnadd
    syl22anc
    wph
    cN
    @115
    @16
    wph
    @114
    @15
    cS
    cdvn
    wph
    @66
    @47
    @114
    @15
    wceq
    #
    @67
    @51
    cS
    cF
    dvn1
    syl2anc
    #
    oveq2d
    fveq1d
    wph
    @117
    @0
    @3
    wph
    c1
    cN
    wph
    1cnd
    wph
    cN
    dvtaylp.n
    nn0cnd
    addcomd
    fveq2d
    3eqtr3d
    dmeqd
    eleqtrrd
    #
    taylplem2
    @14
    @28
    wceq
    #
    @20
    @105
    @21
    @29
    cmul
    @123
    @18
    @103
    @19
    @104
    cdiv
    @123
    cB
    @17
    @102
    @14
    @28
    @16
    fveq2
    fveq1d
    @14
    @28
    cfa
    fveq2
    oveq12d
    @14
    @28
    @9
    cexp
    oveq2
    oveq12d
    fsumshft
    @99
    @109
    @108
    @106
    vk
    csu
    @107
    @99
    @108
    @32
    @106
    vk
    @99
    @2
    @108
    wcel
    #
    wa
    #
    @32
    @7
    @30
    cmul
    co
    @7
    @2
    cmul
    co
    #
    @29
    cmul
    co
    @106
    @125
    @31
    @30
    @7
    cmul
    @125
    @80
    @31
    @30
    wceq
    @125
    @2
    @124
    @78
    @99
    @2
    @0
    elfznn
    adantl
    #
    nnne0d
    #
    @2
    cc0
    cc0
    @30
    ifnefalse
    syl
    oveq2d
    @125
    @7
    @2
    @29
    @125
    wph
    @40
    @43
    wph
    @41
    @124
    simpll
    #
    @124
    @40
    @99
    @108
    @1
    @2
    c1
    cc0
    cuz
    cfv
    wcel
    @108
    @1
    wss
    #
    1eluzge0
    c1
    cc0
    @0
    fzss1
    ax-mp
    #
    sseli
    #
    adantl
    #
    @63
    syl2anc
    #
    @125
    @2
    @127
    nncnd
    #
    @125
    @9
    @28
    @125
    @8
    cB
    wph
    @41
    @124
    simplr
    wph
    @65
    @41
    @124
    @71
    ad2antrr
    subcld
    @125
    @78
    @79
    @127
    @82
    syl
    #
    expcld
    mulassd
    @125
    @126
    @105
    @29
    cmul
    @125
    @5
    @2
    cmul
    co
    #
    @6
    cdiv
    co
    #
    @137
    @104
    @2
    cmul
    co
    #
    cdiv
    co
    #
    @126
    @105
    @125
    @6
    @139
    @137
    cdiv
    @125
    @28
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @104
    @141
    cmul
    co
    #
    @6
    @139
    @125
    @79
    @142
    @143
    wceq
    @136
    @28
    facp1
    syl
    @125
    @141
    @2
    cfa
    @125
    @2
    c1
    @135
    @125
    1cnd
    #
    npcand
    #
    fveq2d
    @125
    @141
    @2
    @104
    cmul
    @145
    oveq2d
    3eqtr3d
    oveq2d
    @125
    wph
    @40
    @138
    @126
    wceq
    @129
    @133
    @44
    @5
    @2
    @6
    @59
    @44
    @2
    @53
    nn0cnd
    @61
    @62
    div23d
    syl2anc
    @125
    @140
    @5
    @104
    cdiv
    co
    @105
    @125
    @5
    @104
    @2
    @125
    wph
    @40
    @5
    cc
    wcel
    @129
    @133
    @59
    syl2anc
    @125
    @104
    @125
    @79
    @104
    cn
    wcel
    @136
    @28
    faccl
    syl
    #
    nncnd
    @135
    @125
    @104
    @146
    nnne0d
    @128
    divcan5rd
    @125
    @5
    @103
    @104
    cdiv
    @125
    cB
    @4
    @102
    @125
    @28
    @115
    cfv
    #
    c1
    @28
    caddc
    co
    #
    @3
    cfv
    #
    @102
    @4
    @125
    @46
    @47
    @119
    @79
    @147
    @149
    wceq
    wph
    @46
    @41
    @124
    dvtaylp.s
    ad2antrr
    wph
    @47
    @41
    @124
    @51
    ad2antrr
    @119
    @125
    1nn0
    a1i
    @136
    cS
    cF
    c1
    @28
    dvnadd
    syl22anc
    @125
    @28
    @115
    @16
    @125
    @114
    @15
    cS
    cdvn
    wph
    @120
    @41
    @124
    @121
    ad2antrr
    oveq2d
    fveq1d
    @125
    @148
    @2
    @3
    @125
    c1
    @2
    @144
    @135
    pncan3d
    fveq2d
    3eqtr3rd
    fveq1d
    oveq1d
    eqtrd
    3eqtr3d
    oveq1d
    3eqtr2d
    sumeq2dv
    @101
    @108
    @106
    vk
    @100
    c1
    @0
    cfz
    0p1e1
    oveq1i
    sumeq1i
    syl6eqr
    @99
    @108
    @1
    @32
    vk
    @130
    @99
    @131
    a1i
    @125
    @7
    @31
    @134
    @124
    @99
    @40
    @85
    @132
    wph
    @40
    @41
    @85
    @86
    an32s
    sylan2
    mulcld
    @99
    @2
    @1
    @108
    cdif
    wcel
    #
    wa
    #
    @32
    @7
    cc0
    cmul
    co
    cc0
    @151
    @31
    cc0
    @7
    cmul
    @151
    @27
    cc0
    @30
    @150
    @99
    @40
    @124
    wn
    #
    wa
    @27
    @2
    @1
    @108
    eldif
    @99
    @40
    @152
    @27
    @99
    @40
    wa
    @124
    @2
    cc0
    @40
    @80
    @124
    wi
    @99
    @40
    @80
    @124
    @40
    @80
    wa
    #
    @2
    c1
    cuz
    cfv
    #
    wcel
    @0
    @2
    cuz
    cfv
    wcel
    #
    @124
    @153
    @2
    cn
    @154
    @40
    @48
    @80
    @78
    @52
    @78
    @48
    @80
    wa
    @81
    biimpri
    sylan
    nnuz
    syl6eleq
    @40
    @155
    @80
    @2
    cc0
    @0
    elfzuz3
    adantr
    @2
    c1
    @0
    elfzuzb
    sylanbrc
    ex
    adantl
    necon1bd
    impr
    sylan2b
    iftrued
    oveq2d
    @151
    @7
    @150
    @99
    @40
    @43
    @2
    @1
    @108
    eldifi
    wph
    @40
    @43
    @41
    @63
    adantlr
    sylan2
    mul01d
    eqtrd
    @99
    cc0
    @0
    fzfid
    fsumss
    3eqtr2rd
    mpteq2dva
    eqtrd
    wph
    @25
    @12
    cc
    cdv
    wph
    vx
    cA
    cB
    cS
    @25
    vk
    cF
    @0
    dvtaylp.s
    dvtaylp.f
    dvtaylp.a
    @58
    dvtaylp.b
    @25
    eqid
    taylpfval
    oveq2d
    wph
    vx
    @110
    cB
    cS
    @26
    vj
    @15
    cN
    dvtaylp.s
    @111
    @112
    dvtaylp.n
    @122
    @26
    eqid
    taylpfval
    3eqtr4d
end
