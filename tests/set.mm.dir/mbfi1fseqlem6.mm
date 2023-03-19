include "cn.mm"
include "citg1.mm"
include "cdm.mm"
include "wf.mm"
include "c0p.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "wral.mm"
include "cmpt.mm"
include "cli.mm"
include "cr.mm"
include "w3a.mm"
include "wex.mm"
include "mbfi1fseqlem4.mm"
include "mbfi1fseqlem5.mm"
include "ralrimiva.mm"
include "wcel.mm"
include "cabs.mm"
include "clt.mm"
include "wrex.mm"
include "simpr.mm"
include "recnd.mm"
include "abscld.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "ffvelrnda.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "readdcld.mm"
include "arch.mm"
include "syl.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmin.mm"
include "cvv.mm"
include "cuz.mm"
include "eqid.mm"
include "cz.mm"
include "nnz.mm"
include "ad2antrl.mm"
include "cn0.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cc.mm"
include "halfcn.mm"
include "a1i.mm"
include "wceq.mm"
include "halfre.mm"
include "0re.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "absid.mm"
include "mp2an.mm"
include "halflt1.mm"
include "eqbrtri.mm"
include "expcnv.mm"
include "nnex.mm"
include "mptex.mm"
include "nnnn0.mm"
include "adantl.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "expcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "weq.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "climsubc2.mm"
include "subid1d.mm"
include "breqtrd.mm"
include "adantr.mm"
include "simprl.mm"
include "eluznn.mm"
include "sylan.mm"
include "ad2antrr.mm"
include "reexpcl.mm"
include "resubcld.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fvex.mm"
include "ad3antrrr.mm"
include "ffvelrnd.mm"
include "i1ff.mm"
include "cmul.mm"
include "cfl.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "nnred.mm"
include "nnne0d.mm"
include "divcan4d.mm"
include "eqcomd.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "eluzelz.mm"
include "exprecd.mm"
include "oveq12d.mm"
include "remulcld.mm"
include "1cnd.mm"
include "divsubdird.mm"
include "fllep1.mm"
include "1red.mm"
include "reflcl.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "wb.mm"
include "peano2rem.mm"
include "nngt0d.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "cneg.mm"
include "cicc.mm"
include "cif.mm"
include "mbfi1fseqlem2.mm"
include "vex.mm"
include "ifex.mm"
include "c0ex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "simprd.mm"
include "addge01d.mm"
include "simplrr.mm"
include "ltled.mm"
include "eluzle.mm"
include "letrd.mm"
include "absled.mm"
include "renegcld.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "iftrued.mm"
include "fveq2d.mm"
include "simpl.mm"
include "ovmpt2a.mm"
include "nndivred.mm"
include "flle.mm"
include "ledivmul2.mm"
include "absge0d.mm"
include "addge02d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "climsqz.mm"
include "rexlimddv.mm"
include "eqeltri.mm"
include "feq1.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "mpteq2dv.mm"
include "breq1d.mm"
include "3anbi123d.mm"
include "spcev.mm"
include "syl3anc.mm"

theorem mbfi1fseqlem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  let cA: class A
  assume mbfi1fseq.1: |- ( ph -> F e. MblFn )
  assume mbfi1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume mbfi1fseq.3: |- J = ( m e. NN , y e. RR |-> ( ( |_ ` ( ( F ` y ) x. ( 2 ^ m ) ) ) / ( 2 ^ m ) ) )
  assume mbfi1fseq.4: |- G = ( m e. NN |-> ( x e. RR |-> if ( x e. ( -u m [,] m ) , if ( ( m J x ) <_ m , ( m J x ) , m ) , 0 ) ) )

  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint F g
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint F m
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint G n
  disjoint G x
  disjoint J m
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint g j
  disjoint g k
  disjoint g z
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
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint k ph
  disjoint A m
  disjoint A x
  disjoint A y
  assert |- ( ph -> E. g ( g : NN --> dom S.1 /\ A. n e. NN ( 0p oR <_ ( g ` n ) /\ ( g ` n ) oR <_ ( g ` ( n + 1 ) ) ) /\ A. x e. RR ( n e. NN |-> ( ( g ` n ) ` x ) ) ~~> ( F ` x ) ) )

  proof
    wph
    cn
    citg1
    cdm
    #
    cG
    wf
    #
    c0p
    vn
    cv
    #
    cG
    cfv
    #
    cle
    cofr
    #
    wbr
    #
    @3
    @2
    c1
    caddc
    co
    #
    cG
    cfv
    #
    @4
    wbr
    #
    wa
    #
    vn
    cn
    wral
    #
    vn
    cn
    vx
    cv
    #
    @3
    cfv
    #
    cmpt
    #
    @11
    cF
    cfv
    #
    cli
    wbr
    #
    vx
    cr
    wral
    #
    cn
    @0
    vg
    cv
    #
    wf
    #
    c0p
    @2
    @17
    cfv
    #
    @4
    wbr
    #
    @19
    @6
    @17
    cfv
    #
    @4
    wbr
    #
    wa
    #
    vn
    cn
    wral
    #
    vn
    cn
    @11
    @19
    cfv
    #
    cmpt
    #
    @14
    cli
    wbr
    #
    vx
    cr
    wral
    #
    w3a
    #
    vg
    wex
    wph
    vx
    vy
    vm
    cF
    cG
    cJ
    mbfi1fseq.1
    mbfi1fseq.2
    mbfi1fseq.3
    mbfi1fseq.4
    mbfi1fseqlem4
    #
    wph
    @9
    vn
    cn
    wph
    vx
    vy
    @2
    vm
    cF
    cG
    cJ
    mbfi1fseq.1
    mbfi1fseq.2
    mbfi1fseq.3
    mbfi1fseq.4
    mbfi1fseqlem5
    ralrimiva
    wph
    @15
    vx
    cr
    wph
    @11
    cr
    wcel
    #
    wa
    #
    @11
    cabs
    cfv
    #
    @14
    caddc
    co
    #
    vk
    cv
    #
    clt
    wbr
    #
    @15
    vk
    cn
    @32
    @34
    cr
    wcel
    #
    @36
    vk
    cn
    wrex
    @32
    @33
    @14
    @32
    @11
    @32
    @11
    wph
    @31
    simpr
    #
    recnd
    #
    abscld
    #
    @32
    @14
    cr
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    @32
    @14
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @41
    @42
    wa
    #
    wph
    cr
    @43
    @11
    cF
    mbfi1fseq.2
    ffvelrnda
    #
    @14
    elrege0
    #
    sylib
    simpld
    #
    readdcld
    #
    @34
    vk
    arch
    syl
    @32
    @35
    cn
    wcel
    #
    @36
    wa
    #
    wa
    #
    @14
    vj
    vn
    cn
    @14
    c1
    c2
    cdiv
    co
    #
    @2
    cexp
    co
    #
    cmin
    co
    #
    cmpt
    #
    @13
    @35
    cvv
    @35
    cuz
    cfv
    #
    @57
    eqid
    @50
    @35
    cz
    wcel
    @32
    @36
    @35
    nnz
    ad2antrl
    @32
    @56
    @14
    cli
    wbr
    @51
    @32
    @56
    @14
    cc0
    cmin
    co
    @14
    cli
    @32
    cc0
    @14
    vj
    vn
    cn0
    @54
    cmpt
    #
    @56
    c1
    cvv
    cn
    nnuz
    @32
    1zzd
    @32
    @53
    vn
    @53
    cc
    wcel
    #
    @32
    halfcn
    a1i
    @53
    cabs
    cfv
    #
    c1
    clt
    wbr
    @32
    @60
    @53
    c1
    clt
    @53
    cr
    wcel
    #
    cc0
    @53
    cle
    wbr
    @60
    @53
    wceq
    halfre
    cc0
    @53
    0re
    halfre
    halfgt0
    ltleii
    @53
    absid
    mp2an
    halflt1
    eqbrtri
    a1i
    expcnv
    @32
    @14
    @48
    recnd
    #
    @56
    cvv
    wcel
    @32
    vn
    cn
    @55
    nnex
    mptex
    a1i
    @32
    vj
    cv
    #
    cn
    wcel
    #
    wa
    #
    @63
    @58
    cfv
    #
    @53
    @63
    cexp
    co
    #
    cc
    @65
    @63
    cn0
    wcel
    #
    @66
    @67
    wceq
    @64
    @68
    @32
    @63
    nnnn0
    #
    adantl
    #
    vn
    @63
    @54
    @67
    cn0
    @58
    @2
    @63
    @53
    cexp
    oveq2
    #
    @58
    eqid
    @53
    @63
    cexp
    ovex
    fvmpt
    syl
    #
    @65
    @59
    @68
    @67
    cc
    wcel
    halfcn
    @70
    @53
    @63
    expcl
    sylancr
    eqeltrd
    @65
    @63
    @56
    cfv
    #
    @14
    @67
    cmin
    co
    #
    @14
    @66
    cmin
    co
    @64
    @73
    @74
    wceq
    #
    @32
    vn
    @63
    @55
    @74
    cn
    @56
    vn
    vj
    weq
    #
    @54
    @67
    @14
    cmin
    @71
    oveq2d
    @56
    eqid
    @14
    @67
    cmin
    ovex
    fvmpt
    #
    adantl
    @65
    @66
    @67
    @14
    cmin
    @72
    oveq2d
    eqtr4d
    climsubc2
    @32
    @14
    @62
    subid1d
    breqtrd
    adantr
    @13
    cvv
    wcel
    @52
    vn
    cn
    @12
    nnex
    mptex
    a1i
    @52
    @63
    @57
    wcel
    #
    wa
    #
    @73
    @74
    cr
    @79
    @64
    @75
    @52
    @50
    @78
    @64
    @32
    @50
    @36
    simprl
    #
    @63
    @35
    eluznn
    sylan
    #
    @77
    syl
    #
    @79
    @14
    @67
    @32
    @41
    @51
    @78
    @48
    ad2antrr
    #
    @79
    @61
    @68
    @67
    cr
    wcel
    halfre
    @79
    @64
    @68
    @81
    @69
    syl
    #
    @53
    @63
    reexpcl
    sylancr
    resubcld
    eqeltrd
    @79
    @63
    @13
    cfv
    #
    @11
    @63
    cG
    cfv
    #
    cfv
    #
    cr
    @79
    @64
    @85
    @87
    wceq
    @81
    vn
    @63
    @12
    @87
    cn
    @13
    @76
    @11
    @3
    @86
    @2
    @63
    cG
    fveq2
    fveq1d
    @13
    eqid
    @11
    @86
    fvex
    fvmpt
    syl
    #
    @79
    cr
    cr
    @11
    @86
    @79
    @86
    @0
    wcel
    cr
    cr
    @86
    wf
    @79
    cn
    @0
    @63
    cG
    wph
    @1
    @31
    @51
    @78
    @30
    ad3antrrr
    @81
    ffvelrnd
    @86
    i1ff
    syl
    @32
    @31
    @51
    @78
    @38
    ad2antrr
    #
    ffvelrnd
    eqeltrd
    @79
    @74
    @14
    c2
    @63
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @90
    cdiv
    co
    #
    @73
    @85
    cle
    @79
    @74
    @91
    c1
    cmin
    co
    #
    @90
    cdiv
    co
    #
    @93
    cle
    @79
    @74
    @91
    @90
    cdiv
    co
    #
    c1
    @90
    cdiv
    co
    #
    cmin
    co
    @95
    @79
    @14
    @96
    @67
    @97
    cmin
    @79
    @96
    @14
    @79
    @14
    @90
    @32
    @14
    cc
    wcel
    @51
    @78
    @62
    ad2antrr
    @79
    @90
    @79
    @90
    @79
    c2
    cn
    wcel
    @68
    @90
    cn
    wcel
    2nn
    @84
    c2
    @63
    nnexpcl
    sylancr
    #
    nnred
    #
    recnd
    #
    @79
    @90
    @98
    nnne0d
    #
    divcan4d
    eqcomd
    @79
    c2
    @63
    @79
    2cnd
    c2
    cc0
    wne
    @79
    2ne0
    a1i
    @78
    @63
    cz
    wcel
    @52
    @35
    @63
    eluzelz
    adantl
    exprecd
    oveq12d
    @79
    @91
    c1
    @90
    @79
    @91
    @79
    @14
    @90
    @83
    @99
    remulcld
    #
    recnd
    @79
    1cnd
    @100
    @101
    divsubdird
    eqtr4d
    @79
    @94
    @92
    cle
    wbr
    #
    @95
    @93
    cle
    wbr
    #
    @79
    @103
    @91
    @92
    c1
    caddc
    co
    cle
    wbr
    #
    @79
    @91
    cr
    wcel
    #
    @105
    @102
    @91
    fllep1
    syl
    @79
    @91
    c1
    @92
    @102
    @79
    1red
    @79
    @106
    @92
    cr
    wcel
    #
    @102
    @91
    reflcl
    syl
    #
    lesubaddd
    mpbird
    @79
    @94
    cr
    wcel
    #
    @107
    @90
    cr
    wcel
    #
    cc0
    @90
    clt
    wbr
    #
    @103
    @104
    wb
    @79
    @106
    @109
    @102
    @91
    peano2rem
    syl
    @108
    @99
    @79
    @90
    @98
    nngt0d
    #
    @94
    @92
    @90
    lediv1
    syl112anc
    mpbid
    eqbrtrd
    @82
    @79
    @85
    @11
    @63
    cneg
    #
    @63
    cicc
    co
    wcel
    #
    @63
    @11
    cJ
    co
    #
    @63
    cle
    wbr
    #
    @115
    @63
    cif
    #
    cc0
    cif
    #
    @117
    @93
    @79
    @85
    @87
    @11
    vx
    cr
    @118
    cmpt
    #
    cfv
    #
    @118
    @88
    @79
    @11
    @86
    @119
    @79
    @64
    @86
    @119
    wceq
    @81
    wph
    vx
    vy
    @63
    vm
    cF
    cG
    cJ
    mbfi1fseq.1
    mbfi1fseq.2
    mbfi1fseq.3
    mbfi1fseq.4
    mbfi1fseqlem2
    syl
    fveq1d
    @79
    @31
    @118
    cvv
    wcel
    @120
    @118
    wceq
    @89
    @114
    @117
    cc0
    @116
    @115
    @63
    @63
    @11
    cJ
    ovex
    vj
    vex
    ifex
    c0ex
    ifex
    vx
    cr
    @118
    cvv
    @119
    @119
    eqid
    fvmpt2
    sylancl
    3eqtrd
    @79
    @114
    @117
    cc0
    @79
    @114
    @31
    @113
    @11
    cle
    wbr
    #
    @11
    @63
    cle
    wbr
    #
    @89
    @79
    @121
    @122
    @79
    @33
    @63
    cle
    wbr
    @121
    @122
    wa
    @79
    @33
    @34
    @63
    @32
    @33
    cr
    wcel
    @51
    @78
    @40
    ad2antrr
    #
    @32
    @37
    @51
    @78
    @49
    ad2antrr
    #
    @79
    @63
    @81
    nnred
    #
    @79
    @42
    @33
    @34
    cle
    wbr
    @79
    @41
    @42
    @79
    @44
    @45
    @32
    @44
    @51
    @78
    @46
    ad2antrr
    @47
    sylib
    simprd
    @79
    @33
    @14
    @123
    @83
    addge01d
    mpbid
    @79
    @34
    @35
    @63
    @124
    @79
    @35
    @52
    @50
    @78
    @80
    adantr
    nnred
    #
    @125
    @79
    @34
    @35
    @124
    @126
    @32
    @50
    @36
    @78
    simplrr
    ltled
    @78
    @35
    @63
    cle
    wbr
    @52
    @35
    @63
    eluzle
    adantl
    letrd
    #
    letrd
    @79
    @11
    @63
    @89
    @125
    absled
    mpbid
    #
    simpld
    @79
    @121
    @122
    @128
    simprd
    @79
    @113
    cr
    wcel
    @63
    cr
    wcel
    @114
    @31
    @121
    @122
    w3a
    wb
    @79
    @63
    @125
    renegcld
    @125
    @113
    @63
    @11
    elicc2
    syl2anc
    mpbir3and
    iftrued
    @79
    @117
    @115
    @93
    @79
    @116
    @115
    @63
    @79
    @115
    @93
    @63
    cle
    @79
    @64
    @31
    @115
    @93
    wceq
    @81
    @89
    vm
    vy
    @63
    @11
    cn
    cr
    vy
    cv
    #
    cF
    cfv
    #
    c2
    vm
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @132
    cdiv
    co
    @93
    cJ
    vm
    vj
    weq
    #
    vy
    vx
    weq
    #
    wa
    #
    @134
    @92
    @132
    @90
    cdiv
    @137
    @133
    @91
    cfl
    @137
    @130
    @14
    @132
    @90
    cmul
    @137
    @129
    @11
    cF
    @135
    @136
    simpr
    fveq2d
    @137
    @131
    @63
    c2
    cexp
    @135
    @136
    simpl
    oveq2d
    #
    oveq12d
    fveq2d
    @138
    oveq12d
    mbfi1fseq.3
    @92
    @90
    cdiv
    ovex
    ovmpt2a
    syl2anc
    #
    @79
    @93
    @14
    @63
    @79
    @92
    @90
    @108
    @98
    nndivred
    @83
    @125
    @79
    @93
    @14
    cle
    wbr
    #
    @92
    @91
    cle
    wbr
    #
    @79
    @106
    @141
    @102
    @91
    flle
    syl
    @79
    @107
    @41
    @110
    @111
    @140
    @141
    wb
    @108
    @83
    @99
    @112
    @92
    @14
    @90
    ledivmul2
    syl112anc
    mpbird
    #
    @79
    @14
    @34
    @63
    @83
    @124
    @125
    @79
    cc0
    @33
    cle
    wbr
    @14
    @34
    cle
    wbr
    @79
    @11
    @32
    @11
    cc
    wcel
    @51
    @78
    @39
    ad2antrr
    absge0d
    @79
    @14
    @33
    @83
    @123
    addge02d
    mpbid
    @127
    letrd
    letrd
    eqbrtrd
    iftrued
    @139
    eqtrd
    3eqtrd
    #
    3brtr4d
    @79
    @85
    @93
    @14
    cle
    @143
    @142
    eqbrtrd
    climsqz
    rexlimddv
    ralrimiva
    @29
    @1
    @10
    @16
    w3a
    vg
    cG
    cG
    vm
    cn
    vx
    cr
    @11
    @131
    cneg
    @131
    cicc
    co
    wcel
    @131
    @11
    cJ
    co
    #
    @131
    cle
    wbr
    @144
    @131
    cif
    cc0
    cif
    cmpt
    #
    cmpt
    cvv
    mbfi1fseq.4
    vm
    cn
    @145
    nnex
    mptex
    eqeltri
    @17
    cG
    wceq
    #
    @18
    @1
    @24
    @10
    @28
    @16
    cn
    @0
    @17
    cG
    feq1
    @146
    @23
    @9
    vn
    cn
    @146
    @20
    @5
    @22
    @8
    @146
    @19
    @3
    c0p
    @4
    @2
    @17
    cG
    fveq1
    #
    breq2d
    @146
    @19
    @3
    @21
    @7
    @4
    @147
    @6
    @17
    cG
    fveq1
    breq12d
    anbi12d
    ralbidv
    @146
    @27
    @15
    vx
    cr
    @146
    @26
    @13
    @14
    cli
    @146
    vn
    cn
    @25
    @12
    @146
    @11
    @19
    @3
    @147
    fveq1d
    mpteq2dv
    breq1d
    ralbidv
    3anbi123d
    spcev
    syl3anc
end
