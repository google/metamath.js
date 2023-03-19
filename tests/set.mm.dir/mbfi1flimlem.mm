include "cn.mm"
include "citg1.mm"
include "cdm.mm"
include "cv.mm"
include "wf.mm"
include "c0p.mm"
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
include "cr.mm"
include "cc0.mm"
include "cif.mm"
include "cli.mm"
include "w3a.mm"
include "wex.mm"
include "cneg.mm"
include "ffvelrnda.mm"
include "cmbf.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "mbfpos.mm"
include "cpnf.mm"
include "cico.mm"
include "wcel.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "max1.mm"
include "sylancr.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "fmptd.mm"
include "mbfi1fseq.mm"
include "renegcld.mm"
include "mbfneg.mm"
include "eeanv.mm"
include "3simpb.mm"
include "anim12i.mm"
include "an4.mm"
include "sylib.mm"
include "r19.26.mm"
include "cmin.mm"
include "cof.mm"
include "cvv.mm"
include "i1fsub.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "nnex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "wb.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ifbieq1d.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "negeqd.mm"
include "negex.mm"
include "anbi12d.mm"
include "nnuz.mm"
include "1zzd.mm"
include "mptex.mm"
include "cc.mm"
include "i1ff.mm"
include "syl.mm"
include "an32s.mm"
include "recnd.mm"
include "adantr.mm"
include "wceq.mm"
include "wfn.mm"
include "ffn.mm"
include "eqidd.mm"
include "ofval.mm"
include "fveq1d.mm"
include "3syl.mm"
include "reex.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "adantlr.mm"
include "climsub.mm"
include "max0sub.mm"
include "breqtrd.mm"
include "ex.mm"
include "sylbid.mm"
include "ralimdva.mm"
include "ovex.mm"
include "feq1.mm"
include "fveq1.mm"
include "mpteq2dv.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "spcev.mm"
include "syl6an.mm"
include "syl5bir.mm"
include "expimpd.mm"
include "syl5.mm"
include "exlimdvv.mm"
include "mp2and.mm"

theorem mbfi1flimlem
  let wph: wff ph
  let vx: setvar x
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vh: setvar h
  let vk: setvar k
  assume mbfi1flim.1: |- ( ph -> F e. MblFn )
  assume mbfi1flimlem.2: |- ( ph -> F : RR --> RR )

  disjoint g n
  disjoint g x
  disjoint n x
  disjoint F g
  disjoint F n
  disjoint F x
  disjoint g ph
  disjoint n ph
  disjoint ph x
  disjoint g y
  disjoint A g
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint g h
  disjoint g k
  disjoint h k
  disjoint h n
  disjoint h x
  disjoint h y
  disjoint F h
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint F y
  disjoint f ph
  disjoint h ph
  disjoint k ph
  disjoint ph y
  assert |- ( ph -> E. g ( g : NN --> dom S.1 /\ A. x e. RR ( n e. NN |-> ( ( g ` n ) ` x ) ) ~~> ( F ` x ) ) )

  proof
    wph
    cn
    citg1
    cdm
    #
    vf
    cv
    #
    wf
    #
    c0p
    vn
    cv
    #
    @1
    cfv
    #
    cle
    cofr
    #
    wbr
    @4
    @3
    c1
    caddc
    co
    #
    @1
    cfv
    @5
    wbr
    wa
    vn
    cn
    wral
    #
    vn
    cn
    vx
    cv
    #
    @4
    cfv
    #
    cmpt
    #
    @8
    vy
    cr
    cc0
    vy
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    @12
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    cli
    wbr
    #
    vx
    cr
    wral
    #
    w3a
    #
    vf
    wex
    #
    cn
    @0
    vh
    cv
    #
    wf
    #
    c0p
    @3
    @21
    cfv
    #
    @5
    wbr
    @23
    @6
    @21
    cfv
    @5
    wbr
    wa
    vn
    cn
    wral
    #
    vn
    cn
    @8
    @23
    cfv
    #
    cmpt
    #
    @8
    vy
    cr
    cc0
    @12
    cneg
    #
    cle
    wbr
    #
    @27
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    cli
    wbr
    #
    vx
    cr
    wral
    #
    w3a
    #
    vh
    wex
    #
    cn
    @0
    vg
    cv
    #
    wf
    #
    vn
    cn
    @8
    @3
    @36
    cfv
    #
    cfv
    #
    cmpt
    #
    @8
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
    wa
    #
    vg
    wex
    #
    wph
    vx
    vf
    vn
    @15
    wph
    vy
    cr
    @12
    wph
    cr
    cr
    @11
    cF
    mbfi1flimlem.2
    ffvelrnda
    #
    wph
    cF
    vy
    cr
    @12
    cmpt
    cmbf
    wph
    vy
    cr
    cr
    cF
    mbfi1flimlem.2
    feqmptd
    mbfi1flim.1
    eqeltrrd
    #
    mbfpos
    wph
    vy
    cr
    @14
    cc0
    cpnf
    cico
    co
    #
    @15
    wph
    @11
    cr
    wcel
    wa
    #
    @14
    cr
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    @14
    @48
    wcel
    @49
    @12
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @50
    @46
    0re
    @13
    @12
    cc0
    cr
    ifcl
    sylancl
    @49
    @53
    @52
    @51
    0re
    @46
    cc0
    @12
    max1
    sylancr
    @14
    elrege0
    sylanbrc
    @15
    eqid
    #
    fmptd
    mbfi1fseq
    wph
    vx
    vh
    vn
    @30
    wph
    vy
    cr
    @27
    @49
    @12
    @46
    renegcld
    #
    wph
    vy
    cr
    @12
    cr
    @46
    @47
    mbfneg
    mbfpos
    wph
    vy
    cr
    @29
    @48
    @30
    @49
    @29
    cr
    wcel
    #
    cc0
    @29
    cle
    wbr
    #
    @29
    @48
    wcel
    @49
    @27
    cr
    wcel
    #
    @53
    @56
    @55
    0re
    @28
    @27
    cc0
    cr
    ifcl
    sylancl
    @49
    @53
    @58
    @57
    0re
    @55
    cc0
    @27
    max1
    sylancr
    @29
    elrege0
    sylanbrc
    @30
    eqid
    #
    fmptd
    mbfi1fseq
    @20
    @35
    wa
    @19
    @34
    wa
    #
    vh
    wex
    vf
    wex
    wph
    @45
    @19
    @34
    vf
    vh
    eeanv
    wph
    @60
    @45
    vf
    vh
    @60
    @2
    @22
    wa
    #
    @18
    @33
    wa
    #
    wa
    #
    wph
    @45
    @60
    @2
    @18
    wa
    #
    @22
    @33
    wa
    #
    wa
    @63
    @19
    @64
    @34
    @65
    @2
    @7
    @18
    3simpb
    @22
    @24
    @33
    3simpb
    anim12i
    @2
    @18
    @22
    @33
    an4
    sylib
    wph
    @61
    @62
    @45
    @62
    @17
    @32
    wa
    #
    vx
    cr
    wral
    #
    wph
    @61
    wa
    #
    @45
    @17
    @32
    vx
    cr
    r19.26
    @68
    cn
    @0
    @1
    @21
    cmin
    cof
    #
    cof
    #
    co
    #
    wf
    #
    @67
    vn
    cn
    @8
    @3
    @71
    cfv
    #
    cfv
    #
    cmpt
    #
    @41
    cli
    wbr
    #
    vx
    cr
    wral
    #
    @45
    @68
    vx
    vy
    cn
    cn
    cn
    @69
    @0
    @0
    @0
    @1
    @21
    cvv
    cvv
    @8
    @0
    wcel
    @11
    @0
    wcel
    wa
    @8
    @11
    @69
    co
    @0
    wcel
    @68
    @8
    @11
    i1fsub
    adantl
    wph
    @2
    @22
    simprl
    #
    wph
    @2
    @22
    simprr
    #
    cn
    cvv
    wcel
    @68
    nnex
    a1i
    #
    @80
    cn
    inidm
    #
    off
    @68
    @66
    @76
    vx
    cr
    @68
    @8
    cr
    wcel
    #
    wa
    #
    @66
    @10
    cc0
    @41
    cle
    wbr
    #
    @41
    cc0
    cif
    #
    cli
    wbr
    #
    @26
    cc0
    @41
    cneg
    #
    cle
    wbr
    #
    @87
    cc0
    cif
    #
    cli
    wbr
    #
    wa
    #
    @76
    @82
    @66
    @91
    wb
    @68
    @82
    @17
    @86
    @32
    @90
    @82
    @16
    @85
    @10
    cli
    vy
    @8
    @14
    @85
    cr
    @15
    vy
    vx
    weq
    #
    @13
    @84
    @12
    @41
    cc0
    @92
    @12
    @41
    cc0
    cle
    @11
    @8
    cF
    fveq2
    #
    breq2d
    @93
    ifbieq1d
    @54
    @84
    @41
    cc0
    @8
    cF
    fvex
    c0ex
    ifex
    fvmpt
    breq2d
    @82
    @31
    @89
    @26
    cli
    vy
    @8
    @29
    @89
    cr
    @30
    @92
    @28
    @88
    @27
    @87
    cc0
    @92
    @27
    @87
    cc0
    cle
    @92
    @12
    @41
    @93
    negeqd
    #
    breq2d
    @94
    ifbieq1d
    @59
    @88
    @87
    cc0
    @41
    negex
    c0ex
    ifex
    fvmpt
    breq2d
    anbi12d
    adantl
    @83
    @91
    @76
    @83
    @91
    wa
    #
    @75
    @85
    @89
    cmin
    co
    #
    @41
    cli
    @95
    @85
    @89
    vk
    @10
    @26
    @75
    c1
    cvv
    cn
    nnuz
    @95
    1zzd
    @83
    @86
    @90
    simprl
    @75
    cvv
    wcel
    @95
    vn
    cn
    @74
    nnex
    mptex
    a1i
    @83
    @86
    @90
    simprr
    @95
    cn
    cc
    vk
    cv
    #
    @10
    @83
    cn
    cc
    @10
    wf
    @91
    @83
    vn
    cn
    @9
    cc
    @10
    @83
    @3
    cn
    wcel
    #
    wa
    #
    @9
    @68
    @98
    @82
    @9
    cr
    wcel
    @68
    @98
    wa
    #
    cr
    cr
    @8
    @4
    @100
    @4
    @0
    wcel
    cr
    cr
    @4
    wf
    @68
    cn
    @0
    @3
    @1
    @78
    ffvelrnda
    @4
    i1ff
    syl
    ffvelrnda
    an32s
    recnd
    @10
    eqid
    #
    fmptd
    adantr
    ffvelrnda
    @95
    cn
    cc
    @97
    @26
    @83
    cn
    cc
    @26
    wf
    @91
    @83
    vn
    cn
    @25
    cc
    @26
    @99
    @25
    @68
    @98
    @82
    @25
    cr
    wcel
    @100
    cr
    cr
    @8
    @23
    @100
    @23
    @0
    wcel
    cr
    cr
    @23
    wf
    @68
    cn
    @0
    @3
    @21
    @79
    ffvelrnda
    @23
    i1ff
    syl
    ffvelrnda
    an32s
    recnd
    @26
    eqid
    #
    fmptd
    adantr
    ffvelrnda
    @83
    @97
    cn
    wcel
    #
    @97
    @75
    cfv
    #
    @97
    @10
    cfv
    #
    @97
    @26
    cfv
    #
    cmin
    co
    #
    wceq
    @91
    @83
    @103
    wa
    @8
    @97
    @71
    cfv
    #
    cfv
    #
    @8
    @97
    @1
    cfv
    #
    cfv
    #
    @8
    @97
    @21
    cfv
    #
    cfv
    #
    cmin
    co
    #
    @104
    @107
    @68
    @103
    @82
    @109
    @114
    wceq
    @68
    @103
    wa
    #
    @82
    wa
    #
    @109
    @8
    @110
    @112
    @69
    co
    #
    cfv
    #
    @114
    @115
    @109
    @118
    wceq
    @82
    @115
    @8
    @108
    @117
    @68
    cn
    cn
    @110
    @112
    @69
    cn
    @1
    @21
    cvv
    cvv
    @97
    @68
    @2
    @1
    cn
    wfn
    @78
    cn
    @0
    @1
    ffn
    syl
    @68
    @22
    @21
    cn
    wfn
    @79
    cn
    @0
    @21
    ffn
    syl
    @80
    @80
    @81
    @115
    @110
    eqidd
    @115
    @112
    eqidd
    ofval
    fveq1d
    adantr
    @115
    cr
    cr
    @111
    @113
    cmin
    cr
    @110
    @112
    cvv
    cvv
    @8
    @115
    @110
    @0
    wcel
    cr
    cr
    @110
    wf
    @110
    cr
    wfn
    @68
    cn
    @0
    @97
    @1
    @78
    ffvelrnda
    @110
    i1ff
    cr
    cr
    @110
    ffn
    3syl
    @115
    @112
    @0
    wcel
    cr
    cr
    @112
    wf
    @112
    cr
    wfn
    @68
    cn
    @0
    @97
    @21
    @79
    ffvelrnda
    @112
    i1ff
    cr
    cr
    @112
    ffn
    3syl
    cr
    cvv
    wcel
    @115
    reex
    a1i
    #
    @119
    cr
    inidm
    @116
    @111
    eqidd
    @116
    @113
    eqidd
    ofval
    eqtrd
    an32s
    @103
    @104
    @109
    wceq
    @83
    vn
    @97
    @74
    @109
    cn
    @75
    vn
    vk
    weq
    #
    @8
    @73
    @108
    @3
    @97
    @71
    fveq2
    fveq1d
    @75
    eqid
    @8
    @108
    fvex
    fvmpt
    adantl
    @103
    @107
    @114
    wceq
    @83
    @103
    @105
    @111
    @106
    @113
    cmin
    vn
    @97
    @9
    @111
    cn
    @10
    @120
    @8
    @4
    @110
    @3
    @97
    @1
    fveq2
    fveq1d
    @101
    @8
    @110
    fvex
    fvmpt
    vn
    @97
    @25
    @113
    cn
    @26
    @120
    @8
    @23
    @112
    @3
    @97
    @21
    fveq2
    fveq1d
    @102
    @8
    @112
    fvex
    fvmpt
    oveq12d
    adantl
    3eqtr4d
    adantlr
    climsub
    @83
    @96
    @41
    wceq
    #
    @91
    @83
    @41
    cr
    wcel
    @121
    @68
    cr
    cr
    @8
    cF
    wph
    cr
    cr
    cF
    wf
    @61
    mbfi1flimlem.2
    adantr
    ffvelrnda
    @41
    max0sub
    syl
    adantr
    breqtrd
    ex
    sylbid
    ralimdva
    @44
    @72
    @77
    wa
    vg
    @71
    @1
    @21
    @70
    ovex
    @36
    @71
    wceq
    #
    @37
    @72
    @43
    @77
    cn
    @0
    @36
    @71
    feq1
    @122
    @42
    @76
    vx
    cr
    @122
    @40
    @75
    @41
    cli
    @122
    vn
    cn
    @39
    @74
    @122
    @8
    @38
    @73
    @3
    @36
    @71
    fveq1
    fveq1d
    mpteq2dv
    breq1d
    ralbidv
    anbi12d
    spcev
    syl6an
    syl5bir
    expimpd
    syl5
    exlimdvv
    syl5bir
    mp2and
end
