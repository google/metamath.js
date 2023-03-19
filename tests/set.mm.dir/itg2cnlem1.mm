include "cr.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "citg2.mm"
include "cxr.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "mpteq2ia.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nffv.mm"
include "nfrn.mm"
include "nfsup.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2.mm"
include "ifbid.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "reex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "cbvmpt.mm"
include "eqtr3i.mm"
include "wa.mm"
include "ccnv.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "cdif.mm"
include "cmbf.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "adantl.mm"
include "wn.mm"
include "wb.mm"
include "nnre.mm"
include "ad2antlr.mm"
include "rexrd.mm"
include "elioopnf.mm"
include "syl.mm"
include "wfn.mm"
include "cico.mm"
include "wf.mm"
include "ffn.mm"
include "ad2antrr.mm"
include "elpreima.mm"
include "simpr.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "wss.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "3bitr4d.mm"
include "notbid.mm"
include "eldif.mm"
include "baib.mm"
include "lenltd.mm"
include "mpteq2dva.mm"
include "3eqtr4a.mm"
include "difss.mm"
include "a1i.mm"
include "cvol.mm"
include "cdm.mm"
include "rembl.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "cres.mm"
include "iftrue.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "mbfima.mm"
include "syl2anc.mm"
include "cmmbl.mm"
include "mbfres.mm"
include "syl5eqel.mm"
include "mbfss.mm"
include "eqeltrd.mm"
include "0e0icopnf.mm"
include "ifcl.mm"
include "adantlr.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "c1.mm"
include "caddc.mm"
include "cofr.mm"
include "wral.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "leidd.mm"
include "ad3antlr.mm"
include "peano2re.mm"
include "lep1d.mm"
include "letrd.mm"
include "iftrued.mm"
include "3brtr4d.mm"
include "iffalse.mm"
include "simprd.mm"
include "0le0.mm"
include "ifboth.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "eqidd.mm"
include "ofrfval2.mm"
include "peano2nn.mm"
include "wrex.mm"
include "breq1.mm"
include "inidm.mm"
include "ofrfval.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "fveq2d.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "itg2mono.mm"
include "ralrn.mm"
include "c0.mm"
include "wne.mm"
include "0re.mm"
include "frn.mm"
include "1nn.mm"
include "dmmptd.mm"
include "syl5eleqr.mm"
include "n0i.mm"
include "dm0rn0.mm"
include "necon3bbii.mm"
include "suprleub.mm"
include "syl31anc.mm"
include "arch.mm"
include "ad2antrl.mm"
include "wi.mm"
include "ltle.mm"
include "syl2an.mm"
include "impr.mm"
include "eqtrd.mm"
include "simprl.mm"
include "fnfvelrn.mm"
include "rexlimddv.mm"
include "suprub.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "eqtr4d.mm"
include "eqtr3d.mm"

theorem itg2cnlem1
  let wph: wff ph
  let vx: setvar x
  let vn: setvar n
  let cF: class F
  let vd: setvar d
  let vm: setvar m
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vw: setvar w
  let cM: class M
  assume itg2cn.1: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2cn.2: |- ( ph -> F e. MblFn )
  assume itg2cn.3: |- ( ph -> ( S.2 ` F ) e. RR )

  disjoint n x
  disjoint F n
  disjoint F x
  disjoint n ph
  disjoint ph x
  disjoint d m
  disjoint d u
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint C d
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint C m
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint C u
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint d n
  disjoint d w
  disjoint F d
  disjoint m n
  disjoint m w
  disjoint F m
  disjoint n u
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint u w
  disjoint F u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint m ph
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint M d
  disjoint M u
  disjoint M x
  assert |- ( ph -> sup ( ran ( n e. NN |-> ( S.2 ` ( x e. RR |-> if ( ( F ` x ) <_ n , ( F ` x ) , 0 ) ) ) ) , RR* , < ) = ( S.2 ` F ) )

  proof
    wph
    vx
    cr
    vn
    cn
    vx
    cv
    #
    cF
    cfv
    #
    vn
    cv
    #
    cle
    wbr
    #
    @1
    cc0
    cif
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    #
    citg2
    cfv
    vn
    cn
    vx
    cr
    @4
    cmpt
    #
    citg2
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cF
    citg2
    cfv
    wph
    vy
    vz
    @13
    vm
    vn
    cn
    @9
    cmpt
    #
    @8
    vx
    cr
    vn
    cn
    @0
    @9
    cfv
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    @8
    vy
    cr
    vm
    cn
    vy
    cv
    #
    vm
    cv
    #
    @14
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cmpt
    vx
    cr
    @18
    @7
    @0
    cr
    wcel
    #
    cr
    @17
    @6
    clt
    @26
    @16
    @5
    @26
    vn
    cn
    @15
    @4
    @26
    @4
    cvv
    wcel
    #
    @15
    @4
    wceq
    @3
    @1
    cc0
    @0
    cF
    fvex
    #
    c0ex
    ifex
    #
    vx
    cr
    @4
    cvv
    @9
    @9
    eqid
    fvmpt2
    mpan2
    mpteq2dv
    rneqd
    supeq1d
    mpteq2ia
    vx
    vy
    cr
    @18
    @25
    vy
    @18
    nfcv
    vx
    @24
    cr
    clt
    vx
    @23
    vx
    vm
    cn
    @22
    vx
    cn
    nfcv
    #
    vx
    @19
    @21
    vx
    @20
    @14
    vx
    vn
    cn
    @9
    @30
    vx
    cr
    @4
    nfmpt1
    nfmpt
    vx
    @20
    nfcv
    nffv
    vx
    @19
    nfcv
    nffv
    nfmpt
    nfrn
    vx
    cr
    nfcv
    vx
    clt
    nfcv
    nfsup
    vx
    vy
    weq
    #
    cr
    @17
    @24
    clt
    @31
    @16
    @23
    @31
    @16
    vn
    cn
    @19
    @9
    cfv
    #
    cmpt
    #
    @23
    @31
    vn
    cn
    @15
    @32
    @0
    @19
    @9
    fveq2
    mpteq2dv
    @33
    vm
    cn
    @19
    vx
    cr
    @1
    @20
    cle
    wbr
    #
    @1
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    cmpt
    @23
    vn
    vm
    cn
    @32
    @37
    vn
    vm
    weq
    #
    @19
    @9
    @36
    @38
    vx
    cr
    @4
    @35
    @38
    @3
    @34
    @1
    cc0
    @2
    @20
    @1
    cle
    breq2
    ifbid
    #
    mpteq2dv
    #
    fveq1d
    cbvmptv
    vm
    cn
    @22
    @37
    @20
    cn
    wcel
    #
    @19
    @21
    @36
    vn
    @20
    @9
    @36
    cn
    @14
    @40
    @14
    eqid
    #
    vx
    cr
    @35
    reex
    mptex
    fvmpt
    #
    fveq1d
    mpteq2ia
    eqtr4i
    syl6eq
    rneqd
    supeq1d
    cbvmpt
    eqtr3i
    wph
    @41
    wa
    #
    @21
    vy
    cr
    @19
    cr
    cF
    ccnv
    @20
    cpnf
    cioo
    co
    #
    cima
    #
    cdif
    #
    wcel
    #
    @19
    cF
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    cmbf
    @44
    @36
    vy
    cr
    @49
    @20
    cle
    wbr
    #
    @49
    cc0
    cif
    #
    cmpt
    @21
    @51
    vx
    vy
    cr
    @35
    @53
    @31
    @34
    @52
    @1
    @49
    cc0
    @31
    @1
    @49
    @20
    cle
    @0
    @19
    cF
    fveq2
    #
    breq1d
    @54
    ifbieq1d
    cbvmptv
    @41
    @21
    @36
    wceq
    #
    wph
    @43
    adantl
    #
    @44
    vy
    cr
    @50
    @53
    @44
    @19
    cr
    wcel
    #
    wa
    #
    @48
    @52
    @49
    cc0
    @58
    @19
    @46
    wcel
    #
    wn
    #
    @20
    @49
    clt
    wbr
    #
    wn
    @48
    @52
    @58
    @59
    @61
    @58
    @49
    @45
    wcel
    #
    @49
    cr
    wcel
    #
    @61
    wa
    #
    @59
    @61
    @58
    @20
    cxr
    wcel
    @62
    @64
    wb
    @58
    @20
    @41
    @20
    cr
    wcel
    #
    wph
    @57
    @20
    nnre
    #
    ad2antlr
    #
    rexrd
    @20
    @49
    elioopnf
    syl
    @58
    @59
    @57
    @62
    wa
    #
    @62
    @58
    cF
    cr
    wfn
    #
    @59
    @68
    wb
    wph
    @69
    @41
    @57
    wph
    cr
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    @69
    itg2cn.1
    cr
    @70
    cF
    ffn
    syl
    #
    ad2antrr
    cr
    @19
    @45
    cF
    elpreima
    syl
    @58
    @57
    @62
    @44
    @57
    simpr
    biantrurd
    bitr4d
    @58
    @63
    @61
    @44
    cr
    cr
    @19
    cF
    wph
    cr
    cr
    cF
    wf
    #
    @41
    wph
    @71
    @70
    cr
    wss
    @73
    itg2cn.1
    rge0ssre
    cr
    @70
    cr
    cF
    fss
    sylancl
    #
    adantr
    ffvelrnda
    #
    biantrurd
    3bitr4d
    notbid
    @57
    @48
    @60
    wb
    @44
    @48
    @57
    @60
    @19
    cr
    @46
    eldif
    baib
    adantl
    @58
    @49
    @20
    @75
    @67
    lenltd
    3bitr4d
    ifbid
    mpteq2dva
    3eqtr4a
    @44
    vy
    @47
    cr
    @50
    cvv
    @47
    cr
    wss
    #
    @44
    cr
    @46
    difss
    #
    a1i
    cr
    cvol
    cdm
    #
    wcel
    @44
    rembl
    a1i
    #
    @50
    cvv
    wcel
    @44
    @48
    wa
    @48
    @49
    cc0
    @19
    cF
    fvex
    c0ex
    ifex
    a1i
    @44
    @19
    cr
    @47
    cdif
    wcel
    #
    wa
    @48
    @49
    cc0
    @80
    @48
    wn
    @44
    @19
    cr
    @47
    eldifn
    adantl
    iffalsed
    wph
    vy
    @47
    @50
    cmpt
    #
    cmbf
    wcel
    @41
    wph
    @81
    vy
    cr
    @49
    cmpt
    #
    @47
    cres
    #
    cmbf
    @81
    vy
    @47
    @49
    cmpt
    #
    @83
    vy
    @47
    @50
    @49
    @48
    @49
    cc0
    iftrue
    mpteq2ia
    @76
    @83
    @84
    wceq
    @77
    vy
    cr
    @47
    @49
    resmpt
    ax-mp
    eqtr4i
    wph
    @82
    cmbf
    wcel
    @47
    @78
    wcel
    #
    @83
    cmbf
    wcel
    wph
    cF
    @82
    cmbf
    wph
    vy
    cr
    @70
    cF
    itg2cn.1
    feqmptd
    itg2cn.2
    eqeltrrd
    wph
    @46
    @78
    wcel
    #
    @85
    wph
    cF
    cmbf
    wcel
    @73
    @86
    itg2cn.2
    @74
    cr
    @20
    cpnf
    cF
    mbfima
    syl2anc
    @46
    cmmbl
    syl
    @47
    @82
    mbfres
    syl2anc
    syl5eqel
    adantr
    mbfss
    eqeltrd
    @44
    cr
    @70
    @21
    wf
    cr
    @70
    @36
    wf
    @44
    vx
    cr
    @35
    @70
    @36
    wph
    @26
    @35
    @70
    wcel
    #
    @41
    wph
    @26
    wa
    #
    @1
    @70
    wcel
    #
    cc0
    @70
    wcel
    @87
    wph
    cr
    @70
    @0
    cF
    itg2cn.1
    ffvelrnda
    #
    0e0icopnf
    @34
    @1
    cc0
    @70
    ifcl
    sylancl
    adantlr
    #
    @36
    eqid
    #
    fmptd
    @44
    cr
    @70
    @21
    @36
    @56
    feq1d
    mpbird
    @44
    @36
    vx
    cr
    @1
    @20
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @1
    cc0
    cif
    #
    cmpt
    #
    @21
    @93
    @14
    cfv
    #
    cle
    cofr
    #
    @44
    @36
    @96
    @98
    wbr
    @35
    @95
    cle
    wbr
    #
    vx
    cr
    wral
    @44
    @99
    vx
    cr
    @44
    @26
    wa
    #
    @34
    @99
    @100
    @34
    wa
    #
    @1
    @1
    @35
    @95
    cle
    @101
    @1
    @100
    @1
    cr
    wcel
    #
    @34
    wph
    @26
    @102
    @41
    @88
    @102
    cc0
    @1
    cle
    wbr
    #
    @88
    @89
    @102
    @103
    wa
    @90
    @1
    elrege0
    sylib
    #
    simpld
    #
    adantlr
    #
    adantr
    #
    leidd
    @34
    @35
    @1
    wceq
    @100
    @34
    @1
    cc0
    iftrue
    adantl
    @101
    @94
    @1
    cc0
    @101
    @1
    @20
    @93
    @107
    @41
    @65
    wph
    @26
    @34
    @66
    ad3antlr
    #
    @101
    @65
    @93
    cr
    wcel
    @108
    @20
    peano2re
    syl
    @100
    @34
    simpr
    @101
    @20
    @108
    lep1d
    letrd
    iftrued
    3brtr4d
    @100
    @34
    wn
    #
    wa
    @35
    cc0
    @95
    cle
    @109
    @35
    cc0
    wceq
    @100
    @34
    @1
    cc0
    iffalse
    adantl
    @100
    cc0
    @95
    cle
    wbr
    #
    @109
    wph
    @26
    @110
    @41
    @88
    @103
    cc0
    cc0
    cle
    wbr
    #
    @110
    @88
    @102
    @103
    @104
    simprd
    #
    0le0
    @94
    @103
    @111
    @110
    @1
    cc0
    @1
    @95
    cc0
    cle
    breq2
    cc0
    @95
    cc0
    cle
    breq2
    ifboth
    sylancl
    adantlr
    adantr
    eqbrtrd
    pm2.61dan
    ralrimiva
    @44
    vx
    cr
    @35
    @95
    cle
    @36
    @96
    @78
    @70
    cvv
    @79
    @91
    @95
    cvv
    wcel
    @100
    @94
    @1
    cc0
    @28
    c0ex
    ifex
    a1i
    @44
    @36
    eqidd
    #
    @44
    @96
    eqidd
    ofrfval2
    mpbird
    @56
    @44
    @93
    cn
    wcel
    #
    @97
    @96
    wceq
    @41
    @114
    wph
    @20
    peano2nn
    adantl
    vn
    @93
    @9
    @96
    cn
    @14
    @2
    @93
    wceq
    #
    vx
    cr
    @4
    @95
    @115
    @3
    @94
    @1
    cc0
    @2
    @93
    @1
    cle
    breq2
    ifbid
    mpteq2dv
    @42
    vx
    cr
    @95
    reex
    mptex
    fvmpt
    syl
    3brtr4d
    wph
    @57
    wa
    #
    @63
    @22
    @49
    cle
    wbr
    #
    vm
    cn
    wral
    #
    @22
    vz
    cv
    #
    cle
    wbr
    #
    vm
    cn
    wral
    #
    vz
    cr
    wrex
    wph
    cr
    cr
    @19
    cF
    @74
    ffvelrnda
    @116
    @117
    vm
    cn
    @116
    @41
    wa
    #
    @22
    @37
    @49
    cle
    @122
    @19
    @21
    @36
    @41
    @55
    @116
    @43
    adantl
    fveq1d
    wph
    @41
    @57
    @37
    @49
    cle
    wbr
    #
    @44
    @123
    vy
    cr
    @44
    @36
    cF
    @98
    wbr
    #
    @123
    vy
    cr
    wral
    @44
    @124
    @35
    @1
    cle
    wbr
    #
    vx
    cr
    wral
    @44
    @125
    vx
    cr
    wph
    @26
    @125
    @41
    @88
    @1
    @1
    cle
    wbr
    #
    @103
    @125
    @88
    @1
    @105
    leidd
    @112
    @34
    @126
    @103
    @125
    @1
    cc0
    @1
    @35
    @1
    cle
    breq1
    cc0
    @35
    @1
    cle
    breq1
    ifboth
    syl2anc
    #
    adantlr
    ralrimiva
    @44
    vx
    cr
    @35
    @1
    cle
    @36
    cF
    cvv
    cvv
    cr
    cr
    cvv
    wcel
    @44
    reex
    a1i
    #
    @35
    cvv
    wcel
    @100
    @34
    @1
    cc0
    @28
    c0ex
    ifex
    #
    a1i
    #
    @106
    @113
    wph
    cF
    vx
    cr
    @1
    cmpt
    #
    wceq
    @41
    wph
    vx
    cr
    @70
    cF
    itg2cn.1
    feqmptd
    #
    adantr
    ofrfval2
    mpbird
    @44
    vy
    cr
    cr
    @37
    @49
    cle
    cr
    @36
    cF
    cvv
    cvv
    @44
    cr
    cvv
    @36
    wf
    @36
    cr
    wfn
    @44
    vx
    cr
    @35
    cvv
    @36
    @130
    @92
    fmptd
    cr
    cvv
    @36
    ffn
    syl
    wph
    @69
    @41
    @72
    adantr
    @128
    @128
    cr
    inidm
    @58
    @37
    eqidd
    @58
    @49
    eqidd
    ofrfval
    mpbid
    r19.21bi
    an32s
    eqbrtrd
    ralrimiva
    @121
    @118
    vz
    @49
    cr
    @119
    @49
    wceq
    @120
    @117
    vm
    cn
    @119
    @49
    @22
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    cxr
    @12
    vm
    cn
    @21
    citg2
    cfv
    #
    cmpt
    #
    crn
    clt
    @11
    @134
    @11
    vm
    cn
    @36
    citg2
    cfv
    #
    cmpt
    @134
    vn
    vm
    cn
    @10
    @135
    @38
    @9
    @36
    citg2
    @40
    fveq2d
    cbvmptv
    vm
    cn
    @133
    @135
    @41
    @21
    @36
    citg2
    @43
    fveq2d
    mpteq2ia
    eqtr4i
    rneqi
    supeq1i
    itg2mono
    wph
    @8
    cF
    citg2
    wph
    @8
    @131
    cF
    wph
    vx
    cr
    @7
    @1
    @88
    @7
    @1
    wceq
    @7
    @1
    cle
    wbr
    #
    @1
    @7
    cle
    wbr
    #
    @88
    @136
    vw
    cv
    #
    @1
    cle
    wbr
    #
    vw
    @6
    wral
    #
    @88
    @140
    @20
    @5
    cfv
    #
    @1
    cle
    wbr
    #
    vm
    cn
    wral
    #
    @88
    @142
    vm
    cn
    @88
    @41
    wa
    @141
    @35
    @1
    cle
    @41
    @141
    @35
    wceq
    #
    @88
    vn
    @20
    @4
    @35
    cn
    @5
    @39
    @5
    eqid
    #
    @129
    fvmpt
    #
    adantl
    @88
    @125
    @41
    @127
    adantr
    eqbrtrd
    ralrimiva
    @88
    @5
    cn
    wfn
    #
    @140
    @143
    wb
    @88
    cn
    cvv
    @5
    wf
    @147
    @88
    vn
    cn
    @4
    cvv
    @5
    @27
    @88
    @2
    cn
    wcel
    #
    wa
    #
    @29
    a1i
    @145
    fmptd
    cn
    cvv
    @5
    ffn
    syl
    #
    @139
    @142
    vw
    vm
    cn
    @5
    @138
    @141
    @1
    cle
    breq1
    ralrn
    syl
    mpbird
    #
    @88
    @6
    cr
    wss
    #
    @6
    c0
    wne
    #
    @138
    @119
    cle
    wbr
    #
    vw
    @6
    wral
    #
    vz
    cr
    wrex
    #
    @102
    @136
    @140
    wb
    @88
    cn
    cr
    @5
    wf
    @152
    @88
    vn
    cn
    @4
    cr
    @5
    @149
    @102
    cc0
    cr
    wcel
    @4
    cr
    wcel
    @88
    @102
    @148
    @105
    adantr
    0re
    @3
    @1
    cc0
    cr
    ifcl
    sylancl
    #
    @145
    fmptd
    cn
    cr
    @5
    frn
    syl
    #
    @88
    c1
    @5
    cdm
    #
    wcel
    #
    @153
    @88
    c1
    cn
    @159
    1nn
    @88
    vn
    @5
    cn
    @4
    cr
    @145
    @157
    dmmptd
    syl5eleqr
    @160
    @159
    c0
    wceq
    #
    wn
    @153
    @159
    c1
    n0i
    @161
    @6
    c0
    @5
    dm0rn0
    necon3bbii
    sylib
    syl
    #
    @88
    @102
    @140
    @156
    @105
    @151
    @155
    @140
    vz
    @1
    cr
    @119
    @1
    wceq
    @154
    @139
    vw
    @6
    @119
    @1
    @138
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    @105
    vz
    vw
    vw
    @6
    @1
    suprleub
    syl31anc
    mpbird
    @88
    @152
    @153
    @156
    @1
    @6
    wcel
    #
    @137
    @158
    @162
    @163
    @88
    @1
    @20
    clt
    wbr
    #
    @164
    vm
    cn
    @88
    @102
    @165
    vm
    cn
    wrex
    @105
    @1
    vm
    arch
    syl
    @88
    @41
    @165
    wa
    #
    wa
    #
    @141
    @1
    @6
    @167
    @141
    @35
    @1
    @41
    @144
    @88
    @165
    @146
    ad2antrl
    @167
    @34
    @1
    cc0
    @88
    @41
    @165
    @34
    @88
    @102
    @65
    @165
    @34
    wi
    @41
    @105
    @66
    @1
    @20
    ltle
    syl2an
    impr
    iftrued
    eqtrd
    @167
    @147
    @41
    @141
    @6
    wcel
    @88
    @147
    @166
    @150
    adantr
    @88
    @41
    @165
    simprl
    cn
    @20
    @5
    fnfvelrn
    syl2anc
    eqeltrrd
    rexlimddv
    vz
    vw
    @6
    @1
    suprub
    syl31anc
    @88
    @7
    @1
    @88
    @152
    @153
    @156
    @7
    cr
    wcel
    @158
    @162
    @163
    vz
    vw
    @6
    suprcl
    syl3anc
    @105
    letri3d
    mpbir2and
    mpteq2dva
    @132
    eqtr4d
    fveq2d
    eqtr3d
end
