include "cn.mm"
include "cv.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cfv.mm"
include "citg1.mm"
include "cmpt.mm"
include "citg2.mm"
include "cli.mm"
include "wbr.mm"
include "wceq.mm"
include "mbfadd.mm"
include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "ge0addcl.mm"
include "adantl.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "cdm.mm"
include "simpl.mm"
include "simpr.mm"
include "i1fadd.mm"
include "nnex.mm"
include "c0p.mm"
include "cle.mm"
include "cofr.mm"
include "c1.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "wral.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "simpld.mm"
include "wi.mm"
include "breq2.mm"
include "feq1.mm"
include "imbi12d.mm"
include "wfn.mm"
include "i1ff.mm"
include "ffn.mm"
include "syl.mm"
include "adantr.mm"
include "cc.mm"
include "csn.mm"
include "cxp.mm"
include "0cn.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "df-0p.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "cnex.mm"
include "wss.mm"
include "cin.mm"
include "ax-resscn.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "0pval.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "biimpa.mm"
include "elrege0.mm"
include "simplbi2.mm"
include "ralimdva.mm"
include "imp.mm"
include "syldan.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "ex.mm"
include "vtoclga.mm"
include "sylc.mm"
include "0plef.mm"
include "sylib.mm"
include "simprd.mm"
include "ofval.mm"
include "breqtrrd.mm"
include "peano2nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "le2addd.mm"
include "ralrimiva.mm"
include "3syl.mm"
include "mpbird.mm"
include "sylan2.mm"
include "3brtr4d.mm"
include "jca.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "mpteq2dv.mm"
include "mptex.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "an32s.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "climadd.mm"
include "syl5eqbrr.mm"
include "readdcld.mm"
include "itg1add.mm"
include "itg1cl.mm"
include "cicc.mm"
include "icossicc.mm"
include "fss.mm"
include "sylancl.mm"
include "itg2i1fseqle.mm"
include "itg2ub.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "breq1d.mm"
include "itg2i1fseq2.mm"
include "itg2i1fseq3.mm"
include "climuni.mm"
include "syl2anc.mm"

theorem itg2addlem
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  assume itg2add.f1: |- ( ph -> F e. MblFn )
  assume itg2add.f2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2add.f3: |- ( ph -> ( S.2 ` F ) e. RR )
  assume itg2add.g1: |- ( ph -> G e. MblFn )
  assume itg2add.g2: |- ( ph -> G : RR --> ( 0 [,) +oo ) )
  assume itg2add.g3: |- ( ph -> ( S.2 ` G ) e. RR )
  assume itg2add.p1: |- ( ph -> P : NN --> dom S.1 )
  assume itg2add.p2: |- ( ph -> A. n e. NN ( 0p oR <_ ( P ` n ) /\ ( P ` n ) oR <_ ( P ` ( n + 1 ) ) ) )
  assume itg2add.p3: |- ( ph -> A. x e. RR ( n e. NN |-> ( ( P ` n ) ` x ) ) ~~> ( F ` x ) )
  assume itg2add.q1: |- ( ph -> Q : NN --> dom S.1 )
  assume itg2add.q2: |- ( ph -> A. n e. NN ( 0p oR <_ ( Q ` n ) /\ ( Q ` n ) oR <_ ( Q ` ( n + 1 ) ) ) )
  assume itg2add.q3: |- ( ph -> A. x e. RR ( n e. NN |-> ( ( Q ` n ) ` x ) ) ~~> ( G ` x ) )

  disjoint n x
  disjoint F n
  disjoint F x
  disjoint P n
  disjoint P x
  disjoint Q n
  disjoint Q x
  disjoint G n
  disjoint G x
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint P f
  disjoint P g
  disjoint P j
  disjoint P k
  disjoint P m
  disjoint P y
  disjoint Q f
  disjoint Q g
  disjoint Q j
  disjoint Q k
  disjoint Q m
  disjoint Q y
  disjoint G f
  disjoint G g
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G y
  disjoint G z
  disjoint f ph
  disjoint g ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( S.2 ` ( F oF + G ) ) = ( ( S.2 ` F ) + ( S.2 ` G ) ) )

  proof
    wph
    vn
    cn
    vn
    cv
    #
    cP
    cQ
    caddc
    cof
    #
    cof
    co
    #
    cfv
    #
    citg1
    cfv
    #
    cmpt
    #
    cF
    cG
    @1
    co
    #
    citg2
    cfv
    #
    cli
    wbr
    @5
    cF
    citg2
    cfv
    #
    cG
    citg2
    cfv
    #
    caddc
    co
    #
    cli
    wbr
    @7
    @10
    wceq
    wph
    vy
    @2
    @5
    vk
    vj
    vm
    @6
    @10
    wph
    cF
    cG
    itg2add.f1
    itg2add.g1
    mbfadd
    wph
    vy
    vz
    cr
    cr
    cr
    caddc
    cc0
    cpnf
    cico
    co
    #
    @11
    @11
    cF
    cG
    cvv
    cvv
    vy
    cv
    #
    @11
    wcel
    vz
    cv
    #
    @11
    wcel
    wa
    @12
    @13
    caddc
    co
    @11
    wcel
    wph
    @12
    @13
    ge0addcl
    adantl
    itg2add.f2
    itg2add.g2
    cr
    cvv
    wcel
    #
    wph
    reex
    a1i
    #
    @15
    cr
    inidm
    #
    off
    wph
    vf
    vg
    cn
    cn
    cn
    @1
    citg1
    cdm
    #
    @17
    @17
    cP
    cQ
    cvv
    cvv
    vf
    cv
    #
    @17
    wcel
    #
    vg
    cv
    #
    @17
    wcel
    #
    wa
    #
    @18
    @20
    @1
    co
    @17
    wcel
    wph
    @22
    @18
    @20
    @19
    @21
    simpl
    @19
    @21
    simpr
    i1fadd
    adantl
    itg2add.p1
    itg2add.q1
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    @23
    cn
    inidm
    #
    off
    wph
    c0p
    vm
    cv
    #
    @2
    cfv
    #
    cle
    cofr
    #
    wbr
    #
    @26
    @25
    c1
    caddc
    co
    #
    @2
    cfv
    #
    @27
    wbr
    #
    wa
    vm
    cn
    wph
    @25
    cn
    wcel
    #
    wa
    #
    @28
    @31
    @33
    c0p
    @25
    cP
    cfv
    #
    @25
    cQ
    cfv
    #
    @1
    co
    #
    @26
    @27
    @33
    cr
    cr
    @36
    wf
    #
    c0p
    @36
    @27
    wbr
    #
    @33
    cr
    @11
    @36
    wf
    @37
    @38
    wa
    @33
    vf
    vg
    cr
    cr
    cr
    caddc
    @11
    @11
    @11
    @34
    @35
    cvv
    cvv
    @18
    @11
    wcel
    @20
    @11
    wcel
    wa
    @18
    @20
    caddc
    co
    @11
    wcel
    @33
    @18
    @20
    ge0addcl
    adantl
    @33
    @34
    @17
    wcel
    #
    c0p
    @34
    @27
    wbr
    #
    cr
    @11
    @34
    wf
    #
    wph
    cn
    @17
    @25
    cP
    itg2add.p1
    ffvelrnda
    #
    @33
    @40
    @34
    @29
    cP
    cfv
    #
    @27
    wbr
    #
    wph
    c0p
    @0
    cP
    cfv
    #
    @27
    wbr
    #
    @45
    @0
    c1
    caddc
    co
    #
    cP
    cfv
    #
    @27
    wbr
    #
    wa
    #
    vn
    cn
    wral
    @32
    @40
    @44
    wa
    #
    itg2add.p2
    @50
    @51
    vn
    @25
    cn
    vn
    vm
    weq
    #
    @46
    @40
    @49
    @44
    @52
    @45
    @34
    c0p
    @27
    @0
    @25
    cP
    fveq2
    #
    breq2d
    @52
    @45
    @34
    @48
    @43
    @27
    @53
    @52
    @47
    @29
    cP
    @0
    @25
    c1
    caddc
    oveq1
    #
    fveq2d
    breq12d
    anbi12d
    rspccva
    sylan
    #
    simpld
    c0p
    @18
    @27
    wbr
    #
    cr
    @11
    @18
    wf
    #
    wi
    #
    @40
    @41
    wi
    vf
    @34
    @17
    @18
    @34
    wceq
    @56
    @40
    @57
    @41
    @18
    @34
    c0p
    @27
    breq2
    cr
    @11
    @18
    @34
    feq1
    imbi12d
    @19
    @56
    @57
    @19
    @56
    wa
    @18
    cr
    wfn
    #
    vx
    cv
    #
    @18
    cfv
    #
    @11
    wcel
    #
    vx
    cr
    wral
    #
    @57
    @19
    @59
    @56
    @19
    cr
    cr
    @18
    wf
    @59
    @18
    i1ff
    #
    cr
    cr
    @18
    ffn
    syl
    #
    adantr
    @19
    @56
    cc0
    @61
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @63
    @19
    @56
    @67
    @19
    vx
    cc
    cr
    cc0
    @61
    cle
    cr
    c0p
    @18
    cvv
    cvv
    c0p
    cc
    wfn
    #
    @19
    @68
    cc
    cc0
    csn
    cxp
    #
    cc
    wfn
    #
    cc0
    cc
    wcel
    @70
    0cn
    cc
    cc0
    cc
    fnconstg
    ax-mp
    cc
    c0p
    @69
    df-0p
    fneq1i
    mpbir
    a1i
    @65
    cc
    cvv
    wcel
    @19
    cnex
    a1i
    @14
    @19
    reex
    a1i
    cr
    cc
    wss
    cc
    cr
    cin
    cr
    wceq
    ax-resscn
    cr
    cc
    sseqin2
    mpbi
    @60
    cc
    wcel
    @60
    c0p
    cfv
    cc0
    wceq
    @19
    @60
    0pval
    adantl
    @19
    @60
    cr
    wcel
    wa
    #
    @61
    eqidd
    ofrfval
    biimpa
    @19
    @67
    @63
    @19
    @66
    @62
    vx
    cr
    @71
    @61
    cr
    wcel
    #
    @66
    @62
    wi
    @19
    cr
    cr
    @60
    @18
    @64
    ffvelrnda
    @62
    @72
    @66
    @61
    elrege0
    simplbi2
    syl
    ralimdva
    imp
    syldan
    vx
    cr
    @11
    @18
    ffnfv
    sylanbrc
    ex
    #
    vtoclga
    sylc
    @33
    @35
    @17
    wcel
    #
    c0p
    @35
    @27
    wbr
    #
    cr
    @11
    @35
    wf
    #
    wph
    cn
    @17
    @25
    cQ
    itg2add.q1
    ffvelrnda
    #
    @33
    @75
    @35
    @29
    cQ
    cfv
    #
    @27
    wbr
    #
    wph
    c0p
    @0
    cQ
    cfv
    #
    @27
    wbr
    #
    @80
    @47
    cQ
    cfv
    #
    @27
    wbr
    #
    wa
    #
    vn
    cn
    wral
    @32
    @75
    @79
    wa
    #
    itg2add.q2
    @84
    @85
    vn
    @25
    cn
    @52
    @81
    @75
    @83
    @79
    @52
    @80
    @35
    c0p
    @27
    @0
    @25
    cQ
    fveq2
    #
    breq2d
    @52
    @80
    @35
    @82
    @78
    @27
    @86
    @52
    @47
    @29
    cQ
    @54
    fveq2d
    breq12d
    anbi12d
    rspccva
    sylan
    #
    simpld
    @58
    @75
    @76
    wi
    vf
    @35
    @17
    @18
    @35
    wceq
    @56
    @75
    @57
    @76
    @18
    @35
    c0p
    @27
    breq2
    cr
    @11
    @18
    @35
    feq1
    imbi12d
    @73
    vtoclga
    sylc
    @14
    @33
    reex
    a1i
    #
    @88
    @16
    off
    @36
    0plef
    sylib
    simprd
    wph
    cn
    cn
    @34
    @35
    @1
    cn
    cP
    cQ
    cvv
    cvv
    @25
    wph
    cn
    @17
    cP
    wf
    #
    cP
    cn
    wfn
    itg2add.p1
    cn
    @17
    cP
    ffn
    syl
    #
    wph
    cn
    @17
    cQ
    wf
    #
    cQ
    cn
    wfn
    itg2add.q1
    cn
    @17
    cQ
    ffn
    syl
    #
    @23
    @23
    @24
    @33
    @34
    eqidd
    @33
    @35
    eqidd
    ofval
    #
    breqtrrd
    @33
    @36
    @43
    @78
    @1
    co
    #
    @26
    @30
    @27
    @33
    @36
    @94
    @27
    wbr
    @12
    @34
    cfv
    #
    @12
    @35
    cfv
    #
    caddc
    co
    #
    @12
    @43
    cfv
    #
    @12
    @78
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    cr
    wral
    @33
    @101
    vy
    cr
    @33
    @12
    cr
    wcel
    #
    wa
    #
    @95
    @96
    @98
    @99
    @33
    cr
    cr
    @12
    @34
    @33
    @39
    cr
    cr
    @34
    wf
    #
    @42
    @34
    i1ff
    syl
    #
    ffvelrnda
    #
    @33
    cr
    cr
    @12
    @35
    @33
    @74
    cr
    cr
    @35
    wf
    #
    @77
    @35
    i1ff
    syl
    #
    ffvelrnda
    #
    @33
    cr
    cr
    @12
    @43
    @33
    @43
    @17
    wcel
    #
    cr
    cr
    @43
    wf
    #
    wph
    @89
    @29
    cn
    wcel
    #
    @110
    @32
    itg2add.p1
    @25
    peano2nn
    #
    cn
    @17
    @29
    cP
    ffvelrn
    syl2an
    #
    @43
    i1ff
    syl
    #
    ffvelrnda
    @33
    cr
    cr
    @12
    @78
    @33
    @78
    @17
    wcel
    #
    cr
    cr
    @78
    wf
    #
    wph
    @91
    @112
    @116
    @32
    itg2add.q1
    @113
    cn
    @17
    @29
    cQ
    ffvelrn
    syl2an
    #
    @78
    i1ff
    syl
    #
    ffvelrnda
    @33
    @95
    @98
    cle
    wbr
    #
    vy
    cr
    @33
    @44
    @120
    vy
    cr
    wral
    @33
    @40
    @44
    @55
    simprd
    @33
    vy
    cr
    cr
    @95
    @98
    cle
    cr
    @34
    @43
    cvv
    cvv
    @33
    @104
    @34
    cr
    wfn
    @105
    cr
    cr
    @34
    ffn
    syl
    #
    @33
    @111
    @43
    cr
    wfn
    @115
    cr
    cr
    @43
    ffn
    syl
    #
    @88
    @88
    @16
    @103
    @95
    eqidd
    #
    @103
    @98
    eqidd
    #
    ofrfval
    mpbid
    r19.21bi
    @33
    @96
    @99
    cle
    wbr
    #
    vy
    cr
    @33
    @79
    @125
    vy
    cr
    wral
    @33
    @75
    @79
    @87
    simprd
    @33
    vy
    cr
    cr
    @96
    @99
    cle
    cr
    @35
    @78
    cvv
    cvv
    @33
    @107
    @35
    cr
    wfn
    @108
    cr
    cr
    @35
    ffn
    syl
    #
    @33
    @117
    @78
    cr
    wfn
    @119
    cr
    cr
    @78
    ffn
    syl
    #
    @88
    @88
    @16
    @103
    @96
    eqidd
    #
    @103
    @99
    eqidd
    #
    ofrfval
    mpbid
    r19.21bi
    le2addd
    ralrimiva
    @33
    vy
    cr
    cr
    @97
    @100
    cle
    cr
    @36
    @94
    cvv
    cvv
    @33
    @36
    @17
    wcel
    @37
    @36
    cr
    wfn
    @33
    @34
    @35
    @42
    @77
    i1fadd
    @36
    i1ff
    cr
    cr
    @36
    ffn
    3syl
    @33
    cr
    cr
    @94
    wf
    #
    @94
    cr
    wfn
    @33
    @94
    @17
    wcel
    @130
    @33
    @43
    @78
    @114
    @118
    i1fadd
    @94
    i1ff
    syl
    cr
    cr
    @94
    ffn
    syl
    @88
    @88
    @16
    @33
    cr
    cr
    @95
    @96
    caddc
    cr
    @34
    @35
    cvv
    cvv
    @12
    @121
    @126
    @88
    @88
    @16
    @123
    @128
    ofval
    #
    @33
    cr
    cr
    @98
    @99
    caddc
    cr
    @43
    @78
    cvv
    cvv
    @12
    @122
    @127
    @88
    @88
    @16
    @124
    @129
    ofval
    ofrfval
    mpbird
    @93
    @32
    wph
    @112
    @30
    @94
    wceq
    @113
    wph
    cn
    cn
    @43
    @78
    @1
    cn
    cP
    cQ
    cvv
    cvv
    @29
    @90
    @92
    @23
    @23
    @24
    wph
    @112
    wa
    #
    @43
    eqidd
    @132
    @78
    eqidd
    ofval
    sylan2
    3brtr4d
    jca
    ralrimiva
    wph
    vm
    cn
    @12
    @26
    cfv
    #
    cmpt
    #
    @12
    @6
    cfv
    #
    cli
    wbr
    vy
    cr
    wph
    @102
    wa
    #
    @134
    @12
    cF
    cfv
    #
    @12
    cG
    cfv
    #
    caddc
    co
    #
    @135
    cli
    @136
    @134
    vn
    cn
    @12
    @3
    cfv
    #
    cmpt
    #
    @139
    cli
    vn
    vm
    cn
    @140
    @133
    @52
    @12
    @3
    @26
    @0
    @25
    @2
    fveq2
    fveq1d
    #
    cbvmptv
    @136
    @137
    @138
    vm
    vn
    cn
    @12
    @45
    cfv
    #
    cmpt
    #
    vn
    cn
    @12
    @80
    cfv
    #
    cmpt
    #
    @141
    c1
    cvv
    cn
    nnuz
    @136
    1zzd
    wph
    vn
    cn
    @60
    @45
    cfv
    #
    cmpt
    #
    @60
    cF
    cfv
    #
    cli
    wbr
    #
    vx
    cr
    wral
    @102
    @144
    @137
    cli
    wbr
    #
    itg2add.p3
    @150
    @151
    vx
    @12
    cr
    vx
    vy
    weq
    #
    @148
    @144
    @149
    @137
    cli
    @152
    vn
    cn
    @147
    @143
    @60
    @12
    @45
    fveq2
    mpteq2dv
    @60
    @12
    cF
    fveq2
    breq12d
    rspccva
    sylan
    @141
    cvv
    wcel
    @136
    vn
    cn
    @140
    nnex
    mptex
    a1i
    wph
    vn
    cn
    @60
    @80
    cfv
    #
    cmpt
    #
    @60
    cG
    cfv
    #
    cli
    wbr
    #
    vx
    cr
    wral
    @102
    @146
    @138
    cli
    wbr
    #
    itg2add.q3
    @156
    @157
    vx
    @12
    cr
    @152
    @154
    @146
    @155
    @138
    cli
    @152
    vn
    cn
    @153
    @145
    @60
    @12
    @80
    fveq2
    mpteq2dv
    @60
    @12
    cG
    fveq2
    breq12d
    rspccva
    sylan
    @136
    @32
    wa
    #
    @25
    @144
    cfv
    #
    @158
    @159
    @95
    cr
    @32
    @159
    @95
    wceq
    @136
    vn
    @25
    @143
    @95
    cn
    @144
    @52
    @12
    @45
    @34
    @53
    fveq1d
    @144
    eqid
    @12
    @34
    fvex
    fvmpt
    adantl
    #
    wph
    @32
    @102
    @95
    cr
    wcel
    @106
    an32s
    eqeltrd
    recnd
    @158
    @25
    @146
    cfv
    #
    @158
    @161
    @96
    cr
    @32
    @161
    @96
    wceq
    @136
    vn
    @25
    @145
    @96
    cn
    @146
    @52
    @12
    @80
    @35
    @86
    fveq1d
    @146
    eqid
    @12
    @35
    fvex
    fvmpt
    adantl
    #
    wph
    @32
    @102
    @96
    cr
    wcel
    @109
    an32s
    eqeltrd
    recnd
    @158
    @133
    @97
    @25
    @141
    cfv
    #
    @159
    @161
    caddc
    co
    wph
    @32
    @102
    @133
    @97
    wceq
    @103
    @133
    @12
    @36
    cfv
    #
    @97
    @33
    @133
    @164
    wceq
    @102
    @33
    @12
    @26
    @36
    @93
    fveq1d
    adantr
    @131
    eqtrd
    an32s
    @32
    @163
    @133
    wceq
    @136
    vn
    @25
    @140
    @133
    cn
    @141
    @142
    @141
    eqid
    @12
    @26
    fvex
    fvmpt
    adantl
    @158
    @159
    @95
    @161
    @96
    caddc
    @160
    @162
    oveq12d
    3eqtr4d
    climadd
    syl5eqbrr
    wph
    cr
    cr
    @137
    @138
    caddc
    cr
    cF
    cG
    cvv
    cvv
    @12
    wph
    cr
    @11
    cF
    wf
    #
    cF
    cr
    wfn
    itg2add.f2
    cr
    @11
    cF
    ffn
    syl
    wph
    cr
    @11
    cG
    wf
    #
    cG
    cr
    wfn
    itg2add.g2
    cr
    @11
    cG
    ffn
    syl
    @15
    @15
    @16
    @136
    @137
    eqidd
    @136
    @138
    eqidd
    ofval
    breqtrrd
    ralrimiva
    vn
    vj
    cn
    @4
    vj
    cv
    #
    @2
    cfv
    #
    citg1
    cfv
    #
    vn
    vj
    weq
    @3
    @168
    citg1
    @0
    @167
    @2
    fveq2
    fveq2d
    cbvmptv
    #
    wph
    @8
    @9
    itg2add.f3
    itg2add.g3
    readdcld
    wph
    @26
    citg1
    cfv
    #
    @10
    cle
    wbr
    #
    vm
    cn
    wral
    vk
    cv
    #
    cn
    wcel
    @173
    @2
    cfv
    #
    citg1
    cfv
    #
    @10
    cle
    wbr
    #
    wph
    @172
    vm
    cn
    @33
    @171
    @34
    citg1
    cfv
    #
    @35
    citg1
    cfv
    #
    caddc
    co
    #
    @10
    cle
    @33
    @171
    @36
    citg1
    cfv
    @179
    @33
    @26
    @36
    citg1
    @93
    fveq2d
    @33
    @34
    @35
    @42
    @77
    itg1add
    eqtrd
    #
    @33
    @177
    @178
    @8
    @9
    @33
    @39
    @177
    cr
    wcel
    @42
    @34
    itg1cl
    syl
    #
    @33
    @74
    @178
    cr
    wcel
    @77
    @35
    itg1cl
    syl
    #
    wph
    @8
    cr
    wcel
    @32
    itg2add.f3
    adantr
    wph
    @9
    cr
    wcel
    @32
    itg2add.g3
    adantr
    @33
    cr
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @39
    @34
    cF
    @27
    wbr
    @177
    @8
    cle
    wbr
    @33
    @165
    @11
    @183
    wss
    #
    @184
    wph
    @165
    @32
    itg2add.f2
    adantr
    cc0
    cpnf
    icossicc
    #
    cr
    @11
    @183
    cF
    fss
    sylancl
    @42
    wph
    vx
    cP
    vn
    cF
    @25
    itg2add.f1
    itg2add.f2
    itg2add.p1
    itg2add.p2
    itg2add.p3
    itg2i1fseqle
    cF
    @34
    itg2ub
    syl3anc
    @33
    cr
    @183
    cG
    wf
    #
    @74
    @35
    cG
    @27
    wbr
    @178
    @9
    cle
    wbr
    @33
    @166
    @185
    @187
    wph
    @166
    @32
    itg2add.g2
    adantr
    @186
    cr
    @11
    @183
    cG
    fss
    sylancl
    @77
    wph
    vx
    cQ
    vn
    cG
    @25
    itg2add.g1
    itg2add.g2
    itg2add.q1
    itg2add.q2
    itg2add.q3
    itg2i1fseqle
    cG
    @35
    itg2ub
    syl3anc
    le2addd
    eqbrtrd
    ralrimiva
    @172
    @176
    vm
    @173
    cn
    vm
    vk
    weq
    #
    @171
    @175
    @10
    cle
    @188
    @26
    @174
    citg1
    @25
    @173
    @2
    fveq2
    fveq2d
    breq1d
    rspccva
    sylan
    itg2i1fseq2
    wph
    @8
    @9
    vm
    vk
    cn
    @173
    cP
    cfv
    #
    citg1
    cfv
    #
    cmpt
    #
    vk
    cn
    @173
    cQ
    cfv
    #
    citg1
    cfv
    #
    cmpt
    #
    @5
    c1
    cvv
    cn
    nnuz
    wph
    1zzd
    wph
    vx
    cP
    @191
    vk
    vn
    cF
    itg2add.f1
    itg2add.f2
    itg2add.p1
    itg2add.p2
    itg2add.p3
    @191
    eqid
    #
    itg2add.f3
    itg2i1fseq3
    @5
    cvv
    wcel
    wph
    vn
    cn
    @4
    nnex
    mptex
    a1i
    wph
    vx
    cQ
    @194
    vk
    vn
    cG
    itg2add.g1
    itg2add.g2
    itg2add.q1
    itg2add.q2
    itg2add.q3
    @194
    eqid
    #
    itg2add.g3
    itg2i1fseq3
    @33
    @25
    @191
    cfv
    #
    @177
    cc
    @32
    @197
    @177
    wceq
    wph
    vk
    @25
    @190
    @177
    cn
    @191
    vk
    vm
    weq
    #
    @189
    @34
    citg1
    @173
    @25
    cP
    fveq2
    fveq2d
    @195
    @34
    citg1
    fvex
    fvmpt
    adantl
    #
    @33
    @177
    @181
    recnd
    eqeltrd
    @33
    @25
    @194
    cfv
    #
    @178
    cc
    @32
    @200
    @178
    wceq
    wph
    vk
    @25
    @193
    @178
    cn
    @194
    @198
    @192
    @35
    citg1
    @173
    @25
    cQ
    fveq2
    fveq2d
    @196
    @35
    citg1
    fvex
    fvmpt
    adantl
    #
    @33
    @178
    @182
    recnd
    eqeltrd
    @33
    @171
    @179
    @25
    @5
    cfv
    #
    @197
    @200
    caddc
    co
    @180
    @32
    @202
    @171
    wceq
    wph
    vj
    @25
    @169
    @171
    cn
    @5
    vj
    vm
    weq
    @168
    @26
    citg1
    @167
    @25
    @2
    fveq2
    fveq2d
    @170
    @26
    citg1
    fvex
    fvmpt
    adantl
    @33
    @197
    @177
    @200
    @178
    caddc
    @199
    @201
    oveq12d
    3eqtr4d
    climadd
    @7
    @10
    @5
    climuni
    syl2anc
end
