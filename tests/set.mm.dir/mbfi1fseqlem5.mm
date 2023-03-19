include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c0p.mm"
include "cfv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cneg.mm"
include "cicc.mm"
include "cif.mm"
include "cr.mm"
include "wral.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "cfl.mm"
include "cdiv.mm"
include "clt.mm"
include "cn0.mm"
include "cpnf.mm"
include "cico.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "ad2antlr.mm"
include "nnred.mm"
include "remulcld.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "mulge0.mm"
include "syl12anc.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0red.mm"
include "nngt0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "wceq.mm"
include "simpr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "adantll.mm"
include "breqtrrd.mm"
include "breq2.mm"
include "ifboth.mm"
include "0le0.mm"
include "sylancl.mm"
include "ralrimiva.mm"
include "cc.mm"
include "cvv.mm"
include "wfn.mm"
include "csn.mm"
include "cxp.mm"
include "0re.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "df-0p.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "a1i.mm"
include "citg1.mm"
include "cdm.mm"
include "mbfi1fseqlem4.mm"
include "i1ff.mm"
include "ffn.mm"
include "3syl.mm"
include "cnex.mm"
include "reex.mm"
include "wss.mm"
include "cin.mm"
include "ax-resscn.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "0pval.mm"
include "adantl.mm"
include "cmpt.mm"
include "mbfi1fseqlem2.mm"
include "fveq1d.mm"
include "rge0ssre.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "sseldi.mm"
include "ad2antrl.mm"
include "reflcl.mm"
include "syl.mm"
include "nndivred.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "fovrn.mm"
include "syl3an1.mm"
include "3expa.mm"
include "nnre.mm"
include "ifcld.mm"
include "ifcl.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "eqtrd.mm"
include "ofrfval.mm"
include "mpbird.mm"
include "mbfi1fseqlem1.mm"
include "ad2antrr.mm"
include "peano2nn.mm"
include "fovrnd.mm"
include "min1.mm"
include "2cn.mm"
include "expp1.mm"
include "eqeltrrd.mm"
include "recnd.mm"
include "2cnd.mm"
include "mulassd.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "flle.mm"
include "wb.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul1.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqtr4d.mm"
include "cz.mm"
include "flcld.mm"
include "2z.mm"
include "zmulcl.mm"
include "flge.mm"
include "eqbrtrd.mm"
include "lemuldiv.mm"
include "syl112anc.mm"
include "3brtr4d.mm"
include "letrd.mm"
include "min2.mm"
include "lep1d.mm"
include "iftrue.mm"
include "renegcld.mm"
include "lenegd.mm"
include "iccss.mm"
include "sselda.mm"
include "iftrued.mm"
include "wn.mm"
include "iffalse.mm"
include "simprd.mm"
include "pm2.61dan.mm"
include "inidm.mm"
include "jca.mm"

theorem mbfi1fseqlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cJ: class J
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  assume mbfi1fseq.1: |- ( ph -> F e. MblFn )
  assume mbfi1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume mbfi1fseq.3: |- J = ( m e. NN , y e. RR |-> ( ( |_ ` ( ( F ` y ) x. ( 2 ^ m ) ) ) / ( 2 ^ m ) ) )
  assume mbfi1fseq.4: |- G = ( m e. NN |-> ( x e. RR |-> if ( x e. ( -u m [,] m ) , if ( ( m J x ) <_ m , ( m J x ) , m ) , 0 ) ) )

  disjoint m x
  disjoint m y
  disjoint F m
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint J m
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint A m
  disjoint A x
  disjoint A y
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
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G g
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint j ph
  disjoint k ph
  disjoint n ph
  assert |- ( ( ph /\ A e. NN ) -> ( 0p oR <_ ( G ` A ) /\ ( G ` A ) oR <_ ( G ` ( A + 1 ) ) ) )

  proof
    wph
    cA
    cn
    wcel
    #
    wa
    #
    c0p
    cA
    cG
    cfv
    #
    cle
    cofr
    #
    wbr
    #
    @2
    cA
    c1
    caddc
    co
    #
    cG
    cfv
    #
    @3
    wbr
    #
    @1
    @4
    cc0
    vx
    cv
    #
    cA
    cneg
    #
    cA
    cicc
    co
    #
    wcel
    #
    cA
    @8
    cJ
    co
    #
    cA
    cle
    wbr
    #
    @12
    cA
    cif
    #
    cc0
    cif
    #
    cle
    wbr
    #
    vx
    cr
    wral
    @1
    @16
    vx
    cr
    @1
    @8
    cr
    wcel
    #
    wa
    #
    cc0
    @14
    cle
    wbr
    #
    cc0
    cc0
    cle
    wbr
    #
    @16
    @18
    cc0
    @12
    cle
    wbr
    #
    cc0
    cA
    cle
    wbr
    #
    @19
    @18
    cc0
    @8
    cF
    cfv
    #
    c2
    cA
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @24
    cdiv
    co
    #
    @12
    cle
    @18
    @26
    cr
    wcel
    #
    cc0
    @26
    cle
    wbr
    @24
    cr
    wcel
    #
    cc0
    @24
    clt
    wbr
    cc0
    @27
    cle
    wbr
    @18
    @26
    @18
    @25
    cr
    wcel
    #
    cc0
    @25
    cle
    wbr
    #
    @26
    cn0
    wcel
    @18
    @23
    @24
    @18
    @23
    cr
    wcel
    #
    cc0
    @23
    cle
    wbr
    #
    @18
    @23
    cc0
    cpnf
    cico
    co
    #
    wcel
    @32
    @33
    wa
    #
    @1
    cr
    @34
    @8
    cF
    wph
    cr
    @34
    cF
    wf
    #
    @0
    mbfi1fseq.2
    adantr
    ffvelrnda
    @23
    elrege0
    sylib
    #
    simpld
    #
    @18
    @24
    @0
    @24
    cn
    wcel
    #
    wph
    @17
    @0
    c2
    cn
    wcel
    #
    cA
    cn0
    wcel
    #
    @39
    2nn
    cA
    nnnn0
    #
    c2
    cA
    nnexpcl
    sylancr
    ad2antlr
    #
    nnred
    #
    remulcld
    #
    @18
    @35
    @29
    cc0
    @24
    cle
    wbr
    @31
    @37
    @44
    @18
    @24
    @18
    @24
    @43
    nnnn0d
    nn0ge0d
    @23
    @24
    mulge0
    syl12anc
    @25
    flge0nn0
    syl2anc
    #
    nn0red
    #
    @18
    @26
    @46
    nn0ge0d
    @44
    @18
    @24
    @43
    nngt0d
    @26
    @24
    divge0
    syl22anc
    @0
    @17
    @12
    @27
    wceq
    wph
    vm
    vy
    cA
    @8
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
    @51
    cdiv
    co
    #
    @27
    cJ
    @50
    cA
    wceq
    #
    @48
    @8
    wceq
    #
    wa
    #
    @53
    @26
    @51
    @24
    cdiv
    @57
    @52
    @25
    cfl
    @57
    @49
    @23
    @51
    @24
    cmul
    @57
    @48
    @8
    cF
    @55
    @56
    simpr
    fveq2d
    @57
    @50
    cA
    c2
    cexp
    @55
    @56
    simpl
    oveq2d
    #
    oveq12d
    fveq2d
    @58
    oveq12d
    mbfi1fseq.3
    @26
    @24
    cdiv
    ovex
    ovmpt2a
    adantll
    #
    breqtrrd
    @0
    @22
    wph
    @17
    @0
    cA
    @42
    nn0ge0d
    ad2antlr
    @13
    @21
    @22
    @19
    @12
    cA
    @12
    @14
    cc0
    cle
    breq2
    cA
    @14
    cc0
    cle
    breq2
    ifboth
    syl2anc
    0le0
    @11
    @19
    @20
    @16
    @14
    cc0
    @14
    @15
    cc0
    cle
    breq2
    cc0
    @15
    cc0
    cle
    breq2
    ifboth
    sylancl
    ralrimiva
    @1
    vx
    cc
    cr
    cc0
    @15
    cle
    cr
    c0p
    @2
    cvv
    cvv
    c0p
    cc
    wfn
    #
    @1
    @60
    cc
    cc0
    csn
    cxp
    #
    cc
    wfn
    #
    cc0
    cr
    wcel
    #
    @62
    0re
    cc
    cc0
    cr
    fnconstg
    ax-mp
    cc
    c0p
    @61
    df-0p
    fneq1i
    mpbir
    a1i
    @1
    @2
    citg1
    cdm
    #
    wcel
    cr
    cr
    @2
    wf
    @2
    cr
    wfn
    wph
    cn
    @64
    cA
    cG
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
    ffvelrnda
    @2
    i1ff
    cr
    cr
    @2
    ffn
    3syl
    #
    cc
    cvv
    wcel
    @1
    cnex
    a1i
    cr
    cvv
    wcel
    @1
    reex
    a1i
    #
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
    @8
    cc
    wcel
    @8
    c0p
    cfv
    cc0
    wceq
    @1
    @8
    0pval
    adantl
    @18
    @8
    @2
    cfv
    #
    @8
    vx
    cr
    @15
    cmpt
    #
    cfv
    #
    @15
    @0
    @68
    @70
    wceq
    wph
    @17
    @0
    @8
    @2
    @69
    wph
    vx
    vy
    cA
    vm
    cF
    cG
    cJ
    mbfi1fseq.1
    mbfi1fseq.2
    mbfi1fseq.3
    mbfi1fseq.4
    mbfi1fseqlem2
    fveq1d
    ad2antlr
    @18
    @17
    @15
    cr
    wcel
    #
    @70
    @15
    wceq
    @1
    @17
    simpr
    #
    @18
    @14
    cr
    wcel
    @63
    @71
    @18
    @13
    @12
    cA
    cr
    wph
    @0
    @17
    @12
    cr
    wcel
    #
    wph
    cn
    cr
    cxp
    #
    cr
    cJ
    wf
    #
    @0
    @17
    @73
    wph
    @54
    cr
    wcel
    #
    vy
    cr
    wral
    vm
    cn
    wral
    @75
    wph
    @76
    vm
    vy
    cn
    cr
    wph
    @50
    cn
    wcel
    #
    @48
    cr
    wcel
    #
    wa
    #
    wa
    #
    @53
    @51
    @80
    @52
    cr
    wcel
    @53
    cr
    wcel
    @80
    @49
    @51
    @80
    @34
    cr
    @49
    rge0ssre
    wph
    @36
    @78
    @49
    @34
    wcel
    @79
    mbfi1fseq.2
    @77
    @78
    simpr
    cr
    @34
    @48
    cF
    ffvelrn
    syl2an
    sseldi
    @80
    @51
    @77
    @51
    cn
    wcel
    #
    wph
    @78
    @77
    @40
    @50
    cn0
    wcel
    @81
    2nn
    @50
    nnnn0
    c2
    @50
    nnexpcl
    sylancr
    ad2antrl
    #
    nnred
    remulcld
    @52
    reflcl
    syl
    @82
    nndivred
    ralrimivva
    vm
    vy
    cn
    cr
    @54
    cr
    cJ
    mbfi1fseq.3
    fmpt2
    sylib
    cA
    @8
    cr
    cn
    cr
    cJ
    fovrn
    syl3an1
    3expa
    #
    @0
    cA
    cr
    wcel
    #
    wph
    @17
    cA
    nnre
    ad2antlr
    #
    ifcld
    #
    0re
    @11
    @14
    cc0
    cr
    ifcl
    sylancl
    vx
    cr
    @15
    cr
    @69
    @69
    eqid
    fvmpt2
    syl2anc
    eqtrd
    #
    ofrfval
    mpbird
    @1
    @7
    @15
    @8
    @5
    cneg
    #
    @5
    cicc
    co
    #
    wcel
    #
    @5
    @8
    cJ
    co
    #
    @5
    cle
    wbr
    #
    @91
    @5
    cif
    #
    cc0
    cif
    #
    cle
    wbr
    #
    vx
    cr
    wral
    @1
    @95
    vx
    cr
    @18
    @11
    @95
    @18
    @11
    wa
    #
    @14
    @93
    @15
    @94
    cle
    @18
    @14
    @93
    cle
    wbr
    #
    @11
    @18
    @14
    @91
    cle
    wbr
    #
    @14
    @5
    cle
    wbr
    #
    @97
    @18
    @14
    @12
    @91
    @86
    @83
    @18
    @91
    cr
    wcel
    #
    cc0
    @91
    cle
    wbr
    #
    @18
    @91
    @34
    wcel
    @100
    @101
    wa
    @18
    @5
    @8
    @34
    cn
    cr
    cJ
    wph
    @74
    @34
    cJ
    wf
    @0
    @17
    wph
    vy
    vm
    cF
    cJ
    mbfi1fseq.1
    mbfi1fseq.2
    mbfi1fseq.3
    mbfi1fseqlem1
    ad2antrr
    @0
    @5
    cn
    wcel
    #
    wph
    @17
    cA
    peano2nn
    #
    ad2antlr
    #
    @72
    fovrnd
    @91
    elrege0
    sylib
    #
    simpld
    #
    @18
    @73
    @84
    @14
    @12
    cle
    wbr
    @83
    @85
    @12
    cA
    min1
    syl2anc
    @18
    @27
    @23
    c2
    @5
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @107
    cdiv
    co
    #
    @12
    @91
    cle
    @18
    @27
    @107
    cmul
    co
    #
    @109
    cle
    wbr
    #
    @27
    @110
    cle
    wbr
    #
    @18
    @111
    @26
    c2
    cmul
    co
    #
    @109
    cle
    @18
    @111
    @27
    @24
    c2
    cmul
    co
    #
    cmul
    co
    @27
    @24
    cmul
    co
    #
    c2
    cmul
    co
    @114
    @18
    @107
    @115
    @27
    cmul
    @18
    c2
    cc
    wcel
    @41
    @107
    @115
    wceq
    2cn
    @0
    @41
    wph
    @17
    @42
    ad2antlr
    c2
    cA
    expp1
    sylancr
    #
    oveq2d
    @18
    @27
    @24
    c2
    @18
    @27
    @18
    @12
    @27
    cr
    @59
    @83
    eqeltrrd
    #
    recnd
    @18
    @24
    @44
    recnd
    #
    @18
    2cnd
    #
    mulassd
    @18
    @116
    @26
    c2
    cmul
    @18
    @26
    @24
    @18
    @26
    @47
    recnd
    @119
    @18
    @24
    @43
    nnne0d
    divcan1d
    oveq1d
    3eqtr2d
    @18
    @114
    @108
    cle
    wbr
    #
    @114
    @109
    cle
    wbr
    #
    @18
    @114
    @25
    c2
    cmul
    co
    #
    @108
    cle
    @18
    @26
    @25
    cle
    wbr
    #
    @114
    @123
    cle
    wbr
    #
    @18
    @30
    @124
    @45
    @25
    flle
    syl
    @18
    @28
    @30
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @124
    @125
    wb
    @47
    @45
    @128
    @18
    @126
    @127
    2re
    2pos
    pm3.2i
    a1i
    @26
    @25
    c2
    lemul1
    syl3anc
    mpbid
    @18
    @108
    @23
    @115
    cmul
    co
    @123
    @18
    @107
    @115
    @23
    cmul
    @117
    oveq2d
    @18
    @23
    @24
    c2
    @18
    @23
    @38
    recnd
    @119
    @120
    mulassd
    eqtr4d
    breqtrrd
    @18
    @108
    cr
    wcel
    #
    @114
    cz
    wcel
    #
    @121
    @122
    wb
    @18
    @23
    @107
    @38
    @18
    @107
    @18
    @40
    @5
    cn0
    wcel
    @107
    cn
    wcel
    2nn
    @18
    @5
    @104
    nnnn0d
    #
    c2
    @5
    nnexpcl
    sylancr
    #
    nnred
    #
    remulcld
    #
    @18
    @26
    cz
    wcel
    c2
    cz
    wcel
    @130
    @18
    @25
    @45
    flcld
    2z
    @26
    c2
    zmulcl
    sylancl
    @108
    @114
    flge
    syl2anc
    mpbid
    eqbrtrd
    @18
    @27
    cr
    wcel
    @109
    cr
    wcel
    #
    @107
    cr
    wcel
    cc0
    @107
    clt
    wbr
    @112
    @113
    wb
    @118
    @18
    @129
    @135
    @134
    @108
    reflcl
    syl
    @133
    @18
    @107
    @132
    nngt0d
    @27
    @109
    @107
    lemuldiv
    syl112anc
    mpbid
    @59
    @18
    @102
    @17
    @91
    @110
    wceq
    @104
    @72
    vm
    vy
    @5
    @8
    cn
    cr
    @54
    @110
    cJ
    @50
    @5
    wceq
    #
    @56
    wa
    #
    @53
    @109
    @51
    @107
    cdiv
    @137
    @52
    @108
    cfl
    @137
    @49
    @23
    @51
    @107
    cmul
    @137
    @48
    @8
    cF
    @136
    @56
    simpr
    fveq2d
    @137
    @50
    @5
    c2
    cexp
    @136
    @56
    simpl
    oveq2d
    #
    oveq12d
    fveq2d
    @138
    oveq12d
    mbfi1fseq.3
    @109
    @107
    cdiv
    ovex
    ovmpt2a
    syl2anc
    3brtr4d
    letrd
    @18
    @14
    cA
    @5
    @86
    @85
    @18
    @5
    @104
    nnred
    #
    @18
    @73
    @84
    @14
    cA
    cle
    wbr
    @83
    @85
    @12
    cA
    min2
    syl2anc
    @18
    cA
    @85
    lep1d
    #
    letrd
    @92
    @98
    @99
    @97
    @91
    @5
    @91
    @93
    @14
    cle
    breq2
    @5
    @93
    @14
    cle
    breq2
    ifboth
    syl2anc
    adantr
    @11
    @15
    @14
    wceq
    @18
    @11
    @14
    cc0
    iftrue
    adantl
    @96
    @90
    @93
    cc0
    @18
    @10
    @89
    @8
    @18
    @88
    cr
    wcel
    @5
    cr
    wcel
    @88
    @9
    cle
    wbr
    #
    cA
    @5
    cle
    wbr
    #
    @10
    @89
    wss
    @18
    @5
    @139
    renegcld
    @139
    @18
    @142
    @141
    @140
    @18
    cA
    @5
    @85
    @139
    lenegd
    mpbid
    @140
    @88
    @5
    @9
    cA
    iccss
    syl22anc
    sselda
    iftrued
    3brtr4d
    @18
    @11
    wn
    #
    wa
    @15
    cc0
    @94
    cle
    @143
    @15
    cc0
    wceq
    @18
    @11
    @14
    cc0
    iffalse
    adantl
    @18
    cc0
    @94
    cle
    wbr
    #
    @143
    @18
    cc0
    @93
    cle
    wbr
    #
    @20
    @144
    @18
    @101
    cc0
    @5
    cle
    wbr
    #
    @145
    @18
    @100
    @101
    @105
    simprd
    @18
    @5
    @131
    nn0ge0d
    @92
    @101
    @146
    @145
    @91
    @5
    @91
    @93
    cc0
    cle
    breq2
    @5
    @93
    cc0
    cle
    breq2
    ifboth
    syl2anc
    0le0
    @90
    @145
    @20
    @144
    @93
    cc0
    @93
    @94
    cc0
    cle
    breq2
    cc0
    @94
    cc0
    cle
    breq2
    ifboth
    sylancl
    adantr
    eqbrtrd
    pm2.61dan
    ralrimiva
    @1
    vx
    cr
    cr
    @15
    @94
    cle
    cr
    @2
    @6
    cvv
    cvv
    @66
    @1
    @6
    @64
    wcel
    #
    cr
    cr
    @6
    wf
    @6
    cr
    wfn
    wph
    cn
    @64
    cG
    wf
    @102
    @147
    @0
    @65
    @103
    cn
    @64
    @5
    cG
    ffvelrn
    syl2an
    @6
    i1ff
    cr
    cr
    @6
    ffn
    3syl
    @67
    @67
    cr
    inidm
    @87
    @18
    @8
    @6
    cfv
    #
    @8
    vx
    cr
    @94
    cmpt
    #
    cfv
    #
    @94
    @18
    @102
    @148
    @150
    wceq
    @104
    @102
    @8
    @6
    @149
    wph
    vx
    vy
    @5
    vm
    cF
    cG
    cJ
    mbfi1fseq.1
    mbfi1fseq.2
    mbfi1fseq.3
    mbfi1fseq.4
    mbfi1fseqlem2
    fveq1d
    syl
    @18
    @17
    @94
    cr
    wcel
    #
    @150
    @94
    wceq
    @72
    @18
    @93
    cr
    wcel
    @63
    @151
    @18
    @92
    @91
    @5
    cr
    @106
    @139
    ifcld
    0re
    @90
    @93
    cc0
    cr
    ifcl
    sylancl
    vx
    cr
    @94
    cr
    @149
    @149
    eqid
    fvmpt2
    syl2anc
    eqtrd
    ofrfval
    mpbird
    jca
end
