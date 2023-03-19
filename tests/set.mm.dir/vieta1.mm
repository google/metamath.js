include "cc.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cdgr.mm"
include "wceq.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cima.mm"
include "chash.mm"
include "wa.mm"
include "csu.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "ccoe.mm"
include "cdiv.mm"
include "cneg.mm"
include "wi.mm"
include "wral.mm"
include "plyssc.mm"
include "sseldi.mm"
include "cn.mm"
include "caddc.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "cn0.mm"
include "wf.mm"
include "eqid.mm"
include "coef3.mm"
include "adantr.mm"
include "0nn0.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "1nn0.mm"
include "simpr.mm"
include "fveq2d.mm"
include "c0p.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrrd.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "wb.mm"
include "dgreq0.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "eqnetrd.mm"
include "divcld.mm"
include "negcld.mm"
include "id.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "cfn.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "cle.mm"
include "fta1.mm"
include "syldan.mm"
include "simpld.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "coeid2.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "nn0uz.mm"
include "1e0p1.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "ffvelrnda.mm"
include "expcl.mm"
include "sylan.mm"
include "mulcld.mm"
include "cz.mm"
include "0z.mm"
include "exp0d.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "fsum1.mm"
include "sylancr.mm"
include "jctil.mm"
include "exp1d.mm"
include "mulneg2d.mm"
include "divcan2d.mm"
include "negeqd.mm"
include "3eqtrd.mm"
include "negidd.mm"
include "fsump1i.mm"
include "simprd.mm"
include "3eqtr2d.mm"
include "wfn.mm"
include "plyf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "snssd.mm"
include "hashsng.mm"
include "simprr.mm"
include "eqtr4d.mm"
include "snfi.mm"
include "hashen.mm"
include "fisseneq.mm"
include "syl3anc.mm"
include "1m1e0.mm"
include "oveq1d.mm"
include "syl5eqr.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "rgen.mm"
include "cbvsumv.mm"
include "eqeq1i.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "w3a.mm"
include "cidp.mm"
include "cxp.mm"
include "cof.mm"
include "cquot.mm"
include "simp1r.mm"
include "simp3r.mm"
include "simp1l.mm"
include "simp3l.mm"
include "simp2.mm"
include "sylib.mm"
include "vieta1lem2.mm"
include "3exp.mm"
include "syl5bir.mm"
include "ralrimdva.mm"
include "eqeq2d.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "fveq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "syl6ib.mm"
include "nnind.mm"
include "syl6eqr.mm"
include "biantrur.mm"
include "syl6bbr.mm"
include "rspcv.mm"
include "syl3c.mm"

theorem vieta1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let cD: class D
  let vf: setvar f
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let cQ: class Q
  let vd: setvar d
  let vg: setvar g
  assume vieta1.1: |- A = ( coeff ` F )
  assume vieta1.2: |- N = ( deg ` F )
  assume vieta1.3: |- R = ( `' F " { 0 } )
  assume vieta1.4: |- ( ph -> F e. ( Poly ` S ) )
  assume vieta1.5: |- ( ph -> ( # ` R ) = N )
  assume vieta1.6: |- ( ph -> N e. NN )

  disjoint R x
  disjoint ph x
  disjoint D f
  disjoint F f
  disjoint f k
  disjoint f y
  disjoint f z
  disjoint N f
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint f x
  disjoint Q f
  disjoint k x
  disjoint Q k
  disjoint Q x
  disjoint d f
  disjoint d g
  disjoint d k
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint f g
  disjoint R f
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint R g
  disjoint R k
  disjoint x y
  disjoint x z
  disjoint R y
  disjoint R z
  disjoint A f
  disjoint A z
  disjoint k ph
  disjoint ph z
  assert |- ( ph -> sum_ x e. R x = -u ( ( A ` ( N - 1 ) ) / ( A ` N ) ) )

  proof
    wph
    cF
    cc
    cply
    cfv
    #
    wcel
    cN
    vf
    cv
    #
    cdgr
    cfv
    #
    wceq
    #
    @1
    ccnv
    #
    cc0
    csn
    #
    cima
    #
    chash
    cfv
    #
    @2
    wceq
    #
    wa
    #
    @6
    vx
    cv
    #
    vx
    csu
    #
    @2
    c1
    cmin
    co
    #
    @1
    ccoe
    cfv
    #
    cfv
    #
    @2
    @13
    cfv
    #
    cdiv
    co
    #
    cneg
    #
    wceq
    #
    wi
    #
    vf
    @0
    wral
    #
    cR
    chash
    cfv
    #
    cN
    wceq
    #
    cR
    @10
    vx
    csu
    #
    cN
    c1
    cmin
    co
    #
    cA
    cfv
    #
    cN
    cA
    cfv
    #
    cdiv
    co
    #
    cneg
    #
    wceq
    #
    wph
    cS
    cply
    cfv
    @0
    cF
    cS
    plyssc
    vieta1.4
    sseldi
    wph
    cN
    cn
    wcel
    @20
    vieta1.6
    vy
    cv
    #
    @2
    wceq
    #
    @8
    wa
    #
    @18
    wi
    #
    vf
    @0
    wral
    c1
    @2
    wceq
    #
    @8
    wa
    #
    @18
    wi
    #
    vf
    @0
    wral
    vd
    cv
    #
    @2
    wceq
    #
    @8
    wa
    #
    @18
    wi
    #
    vf
    @0
    wral
    #
    @37
    c1
    caddc
    co
    #
    @2
    wceq
    #
    @8
    wa
    #
    @18
    wi
    #
    vf
    @0
    wral
    #
    @20
    vy
    vd
    cN
    @30
    c1
    wceq
    #
    @33
    @36
    vf
    @0
    @47
    @32
    @35
    @18
    @47
    @31
    @34
    @8
    @30
    c1
    @2
    eqeq1
    anbi1d
    imbi1d
    ralbidv
    @30
    @37
    wceq
    #
    @33
    @40
    vf
    @0
    @48
    @32
    @39
    @18
    @48
    @31
    @38
    @8
    @30
    @37
    @2
    eqeq1
    anbi1d
    imbi1d
    ralbidv
    @30
    @42
    wceq
    #
    @33
    @45
    vf
    @0
    @49
    @32
    @44
    @18
    @49
    @31
    @43
    @8
    @30
    @42
    @2
    eqeq1
    anbi1d
    imbi1d
    ralbidv
    @30
    cN
    wceq
    #
    @33
    @19
    vf
    @0
    @50
    @32
    @9
    @18
    @50
    @31
    @3
    @8
    @30
    cN
    @2
    eqeq1
    anbi1d
    imbi1d
    ralbidv
    @36
    vf
    @0
    @1
    @0
    wcel
    #
    @35
    @18
    @51
    @35
    wa
    #
    cc0
    @13
    cfv
    #
    c1
    @13
    cfv
    #
    cdiv
    co
    #
    cneg
    #
    csn
    #
    @10
    vx
    csu
    #
    @56
    @11
    @17
    @51
    @34
    @58
    @56
    wceq
    #
    @8
    @51
    @34
    wa
    #
    @56
    cc
    wcel
    #
    @61
    @59
    @60
    @55
    @60
    @53
    @54
    @60
    cn0
    cc
    @13
    wf
    #
    cc0
    cn0
    wcel
    #
    @53
    cc
    wcel
    @51
    @62
    @34
    @13
    cc
    @1
    @13
    eqid
    #
    coef3
    adantr
    #
    0nn0
    cn0
    cc
    cc0
    @13
    ffvelrn
    sylancl
    #
    @60
    @62
    c1
    cn0
    wcel
    #
    @54
    cc
    wcel
    @65
    1nn0
    cn0
    cc
    c1
    @13
    ffvelrn
    sylancl
    #
    @60
    @54
    @15
    cc0
    @60
    c1
    @2
    @13
    @51
    @34
    simpr
    #
    fveq2d
    #
    @60
    @1
    c0p
    wne
    #
    @15
    cc0
    wne
    #
    @60
    @2
    cc0
    wne
    @71
    @60
    c1
    @2
    cc0
    @69
    c1
    cc0
    wne
    @60
    ax-1ne0
    a1i
    eqnetrrd
    @1
    c0p
    @2
    cc0
    @1
    c0p
    wceq
    @2
    c0p
    cdgr
    cfv
    cc0
    @1
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    necon3i
    syl
    #
    @51
    @71
    @72
    wb
    @34
    @51
    @1
    c0p
    @15
    cc0
    @13
    cc
    @1
    @2
    @2
    eqid
    #
    @64
    dgreq0
    necon3bid
    adantr
    mpbid
    eqnetrd
    #
    divcld
    #
    negcld
    #
    @77
    @10
    @56
    vx
    @56
    cc
    @10
    @56
    wceq
    id
    sumsn
    syl2anc
    adantrr
    @52
    @57
    @6
    @10
    vx
    @52
    @6
    cfn
    wcel
    #
    @57
    @6
    wss
    #
    @57
    @6
    cen
    wbr
    #
    @57
    @6
    wceq
    @51
    @34
    @78
    @8
    @60
    @78
    @7
    @2
    cle
    wbr
    #
    @51
    @34
    @71
    @78
    @81
    wa
    @73
    @6
    cc
    @1
    @6
    eqid
    fta1
    syldan
    simpld
    #
    adantrr
    @51
    @34
    @79
    @8
    @60
    @56
    @6
    @60
    @56
    @6
    wcel
    #
    @61
    @56
    @1
    cfv
    #
    cc0
    wceq
    #
    @77
    @60
    @84
    cc0
    @2
    cfz
    co
    #
    vk
    cv
    #
    @13
    cfv
    #
    @56
    @87
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    c1
    cfz
    co
    #
    @90
    vk
    csu
    #
    cc0
    @51
    @34
    @61
    @84
    @91
    wceq
    @77
    @13
    cc
    vk
    @1
    @2
    @56
    @64
    @74
    coeid2
    syldan
    @60
    @92
    @86
    @90
    vk
    @60
    c1
    @2
    cc0
    cfz
    @69
    oveq2d
    sumeq1d
    @60
    @67
    @93
    cc0
    wceq
    @60
    @90
    @54
    @56
    c1
    cexp
    co
    #
    cmul
    co
    #
    @53
    cc0
    vk
    cc0
    cc0
    c1
    cn0
    nn0uz
    1e0p1
    @87
    c1
    wceq
    @88
    @54
    @89
    @94
    cmul
    @87
    c1
    @13
    fveq2
    @87
    c1
    @56
    cexp
    oveq2
    oveq12d
    @60
    @87
    cn0
    wcel
    #
    wa
    @88
    @89
    @60
    cn0
    cc
    @87
    @13
    @65
    ffvelrnda
    @60
    @61
    @96
    @89
    cc
    wcel
    @77
    @56
    @87
    expcl
    sylan
    mulcld
    @60
    cc0
    cc0
    cfz
    co
    @90
    vk
    csu
    #
    @53
    wceq
    @63
    @60
    @97
    @53
    @56
    cc0
    cexp
    co
    #
    cmul
    co
    #
    @53
    @60
    cc0
    cz
    wcel
    @99
    cc
    wcel
    @97
    @99
    wceq
    0z
    @60
    @99
    @53
    cc
    @60
    @99
    @53
    c1
    cmul
    co
    @53
    @60
    @98
    c1
    @53
    cmul
    @60
    @56
    @77
    exp0d
    oveq2d
    @60
    @53
    @66
    mulid1d
    eqtrd
    #
    @66
    eqeltrd
    @90
    @99
    vk
    cc0
    @87
    cc0
    wceq
    @88
    @53
    @89
    @98
    cmul
    @87
    cc0
    @13
    fveq2
    @87
    cc0
    @56
    cexp
    oveq2
    oveq12d
    fsum1
    sylancr
    @100
    eqtrd
    0nn0
    jctil
    @60
    @53
    @95
    caddc
    co
    @53
    @53
    cneg
    #
    caddc
    co
    cc0
    @60
    @95
    @101
    @53
    caddc
    @60
    @95
    @54
    @56
    cmul
    co
    @54
    @55
    cmul
    co
    #
    cneg
    @101
    @60
    @94
    @56
    @54
    cmul
    @60
    @56
    @77
    exp1d
    oveq2d
    @60
    @54
    @55
    @68
    @76
    mulneg2d
    @60
    @102
    @53
    @60
    @53
    @54
    @66
    @68
    @75
    divcan2d
    negeqd
    3eqtrd
    oveq2d
    @60
    @53
    @66
    negidd
    eqtrd
    fsump1i
    simprd
    3eqtr2d
    @60
    @1
    cc
    wfn
    #
    @83
    @61
    @85
    wa
    wb
    @51
    @103
    @34
    @51
    cc
    cc
    @1
    wf
    @103
    cc
    @1
    plyf
    cc
    cc
    @1
    ffn
    syl
    adantr
    cc
    cc0
    @56
    @1
    fniniseg
    syl
    mpbir2and
    snssd
    adantrr
    @52
    @57
    chash
    cfv
    #
    @7
    wceq
    #
    @80
    @52
    @104
    @2
    @7
    @51
    @34
    @104
    @2
    wceq
    @8
    @60
    @104
    c1
    @2
    @60
    @61
    @104
    c1
    wceq
    @77
    @56
    cc
    hashsng
    syl
    @69
    eqtrd
    adantrr
    @51
    @34
    @8
    simprr
    eqtr4d
    @51
    @34
    @105
    @80
    wb
    #
    @8
    @60
    @57
    cfn
    wcel
    @78
    @106
    @56
    snfi
    @82
    @57
    @6
    hashen
    sylancr
    adantrr
    mpbid
    @57
    @6
    fisseneq
    syl3anc
    sumeq1d
    @51
    @34
    @56
    @17
    wceq
    @8
    @60
    @55
    @16
    @60
    @53
    @14
    @54
    @15
    cdiv
    @60
    cc0
    @12
    @13
    @60
    cc0
    c1
    c1
    cmin
    co
    @12
    1m1e0
    @60
    c1
    @2
    c1
    cmin
    @69
    oveq1d
    syl5eqr
    fveq2d
    @70
    oveq12d
    negeqd
    adantrr
    3eqtr3d
    ex
    rgen
    @37
    cn
    wcel
    #
    @41
    @42
    vg
    cv
    #
    cdgr
    cfv
    #
    wceq
    #
    @108
    ccnv
    #
    @5
    cima
    #
    chash
    cfv
    #
    @109
    wceq
    #
    wa
    #
    @112
    @10
    vx
    csu
    #
    @109
    c1
    cmin
    co
    #
    @108
    ccoe
    cfv
    #
    cfv
    #
    @109
    @118
    cfv
    #
    cdiv
    co
    #
    cneg
    #
    wceq
    #
    wi
    #
    vg
    @0
    wral
    @46
    @107
    @41
    @124
    vg
    @0
    @41
    @39
    @6
    @30
    vy
    csu
    #
    @17
    wceq
    #
    wi
    #
    vf
    @0
    wral
    #
    @107
    @108
    @0
    wcel
    #
    wa
    #
    @124
    @127
    @40
    vf
    @0
    @126
    @18
    @39
    @125
    @11
    @17
    @6
    @30
    @10
    vy
    vx
    @30
    @10
    wceq
    id
    cbvsumv
    eqeq1i
    imbi2i
    ralbii
    #
    @130
    @128
    @115
    @123
    @130
    @128
    @115
    w3a
    #
    vx
    vz
    @118
    @37
    @108
    cidp
    cc
    vz
    cv
    csn
    cxp
    cmin
    cof
    co
    cquot
    co
    #
    @112
    cc
    vf
    @108
    @109
    @118
    eqid
    @109
    eqid
    @112
    eqid
    @107
    @129
    @128
    @115
    simp1r
    @130
    @128
    @110
    @114
    simp3r
    @107
    @129
    @128
    @115
    simp1l
    @130
    @128
    @110
    @114
    simp3l
    @132
    @128
    @41
    @130
    @128
    @115
    simp2
    @131
    sylib
    @133
    eqid
    vieta1lem2
    3exp
    syl5bir
    ralrimdva
    @124
    @45
    vg
    vf
    @0
    @108
    @1
    wceq
    #
    @115
    @44
    @123
    @18
    @134
    @110
    @43
    @114
    @8
    @134
    @109
    @2
    @42
    @108
    @1
    cdgr
    fveq2
    #
    eqeq2d
    @134
    @113
    @7
    @109
    @2
    @134
    @112
    @6
    chash
    @134
    @111
    @4
    @5
    @108
    @1
    cnveq
    imaeq1d
    #
    fveq2d
    @135
    eqeq12d
    anbi12d
    @134
    @116
    @11
    @122
    @17
    @134
    @112
    @6
    @10
    vx
    @136
    sumeq1d
    @134
    @121
    @16
    @134
    @119
    @14
    @120
    @15
    cdiv
    @134
    @117
    @12
    @118
    @13
    @108
    @1
    ccoe
    fveq2
    #
    @134
    @109
    @2
    c1
    cmin
    @135
    oveq1d
    fveq12d
    @134
    @109
    @2
    @118
    @13
    @137
    @135
    fveq12d
    oveq12d
    negeqd
    eqeq12d
    imbi12d
    cbvralv
    syl6ib
    nnind
    syl
    vieta1.5
    @19
    @22
    @29
    wi
    vf
    cF
    @0
    @1
    cF
    wceq
    #
    @9
    @22
    @18
    @29
    @138
    @9
    cN
    cF
    cdgr
    cfv
    #
    wceq
    #
    @22
    wa
    @22
    @138
    @3
    @140
    @8
    @22
    @138
    @2
    @139
    cN
    @1
    cF
    cdgr
    fveq2
    #
    eqeq2d
    @138
    @7
    @21
    @2
    cN
    @138
    @6
    cR
    chash
    @138
    @6
    cF
    ccnv
    #
    @5
    cima
    cR
    @138
    @4
    @142
    @5
    @1
    cF
    cnveq
    imaeq1d
    vieta1.3
    syl6eqr
    #
    fveq2d
    @138
    @2
    @139
    cN
    @141
    vieta1.2
    syl6eqr
    #
    eqeq12d
    anbi12d
    @140
    @22
    vieta1.2
    biantrur
    syl6bbr
    @138
    @11
    @23
    @17
    @28
    @138
    @6
    cR
    @10
    vx
    @143
    sumeq1d
    @138
    @16
    @27
    @138
    @14
    @25
    @15
    @26
    cdiv
    @138
    @12
    @24
    @13
    cA
    @138
    @13
    cF
    ccoe
    cfv
    cA
    @1
    cF
    ccoe
    fveq2
    vieta1.1
    syl6eqr
    #
    @138
    @2
    cN
    c1
    cmin
    @144
    oveq1d
    fveq12d
    @138
    @2
    cN
    @13
    cA
    @145
    @144
    fveq12d
    oveq12d
    negeqd
    eqeq12d
    imbi12d
    rspcv
    syl3c
end
