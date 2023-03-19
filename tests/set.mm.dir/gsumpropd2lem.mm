include "crn.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "c0g.mm"
include "cdm.mm"
include "cfz.mm"
include "wcel.mm"
include "cseq.mm"
include "cuz.mm"
include "wrex.mm"
include "wex.mm"
include "cio.mm"
include "c1.mm"
include "chash.mm"
include "wf1o.mm"
include "ccom.mm"
include "cif.mm"
include "cgsu.mm"
include "adantr.mm"
include "wb.mm"
include "eqeq1d.mm"
include "oveqrspc2v.mm"
include "ancom2s.mm"
include "anbi12d.mm"
include "anassrs.mm"
include "raleqbidva.mm"
include "rabeqbidva.mm"
include "sseq2d.mm"
include "eqidd.mm"
include "grpidpropd.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "wfun.mm"
include "simpr.mm"
include "simplrr.mm"
include "eleqtrrd.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "adantlr.mm"
include "seqfeq4.mm"
include "eqeq2d.mm"
include "pm5.32da.mm"
include "rexbidva.mm"
include "exbidv.mm"
include "iotabidv.mm"
include "ccnv.mm"
include "cvv.mm"
include "cdif.mm"
include "cima.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "ad3antrrr.mm"
include "f1ofun.mm"
include "ad3antlr.mm"
include "f1odm.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "fvco.mm"
include "difpreima.mm"
include "syl.mm"
include "syl5eq.mm"
include "difss.mm"
include "syl6eqss.mm"
include "dfdm4.mm"
include "dfrn4.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "simpll.mm"
include "caovclg.mm"
include "sylan.mm"
include "wn.mm"
include "c0.mm"
include "cz.mm"
include "wfn.mm"
include "1z.mm"
include "seqfn.mm"
include "fndm.mm"
include "mp2b.mm"
include "eleq2i.mm"
include "sylnibr.mm"
include "ndmfv.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"
include "f1oeq2.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "anbi1d.mm"
include "ifeq12d.mm"
include "ifbieq12d.mm"
include "eqid.mm"
include "a1i.mm"
include "gsumvalx.mm"
include "3eqtr4d.mm"

theorem gsumpropd2lem
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume gsumpropd2.f: |- ( ph -> F e. V )
  assume gsumpropd2.g: |- ( ph -> G e. W )
  assume gsumpropd2.h: |- ( ph -> H e. X )
  assume gsumpropd2.b: |- ( ph -> ( Base ` G ) = ( Base ` H ) )
  assume gsumpropd2.c: |- ( ( ph /\ ( s e. ( Base ` G ) /\ t e. ( Base ` G ) ) ) -> ( s ( +g ` G ) t ) e. ( Base ` G ) )
  assume gsumpropd2.e: |- ( ( ph /\ ( s e. ( Base ` G ) /\ t e. ( Base ` G ) ) ) -> ( s ( +g ` G ) t ) = ( s ( +g ` H ) t ) )
  assume gsumpropd2.n: |- ( ph -> Fun F )
  assume gsumpropd2.r: |- ( ph -> ran F C_ ( Base ` G ) )
  assume gsumprop2dlem.1: |- A = ( `' F " ( _V \ { s e. ( Base ` G ) | A. t e. ( Base ` G ) ( ( s ( +g ` G ) t ) = t /\ ( t ( +g ` G ) s ) = t ) } ) )
  assume gsumprop2dlem.2: |- B = ( `' F " ( _V \ { s e. ( Base ` H ) | A. t e. ( Base ` H ) ( ( s ( +g ` H ) t ) = t /\ ( t ( +g ` H ) s ) = t ) } ) )

  disjoint s t
  disjoint F s
  disjoint F t
  disjoint G s
  disjoint G t
  disjoint H s
  disjoint H t
  disjoint ph s
  disjoint ph t
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint F a
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint F b
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint F f
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint F m
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint F n
  disjoint s x
  disjoint t x
  disjoint F x
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint H a
  disjoint H b
  disjoint H f
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> ( G gsum F ) = ( H gsum F ) )

  proof
    wph
    cF
    crn
    #
    vs
    cv
    #
    vt
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    wceq
    #
    @2
    @1
    @3
    co
    #
    @2
    wceq
    #
    wa
    #
    vt
    cG
    cbs
    cfv
    #
    wral
    #
    vs
    @9
    crab
    #
    wss
    #
    cG
    c0g
    cfv
    #
    cF
    cdm
    #
    cfz
    crn
    wcel
    #
    @14
    vm
    cv
    #
    vn
    cv
    #
    cfz
    co
    #
    wceq
    #
    vx
    cv
    #
    @17
    @3
    cF
    @16
    cseq
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @16
    cuz
    cfv
    #
    wrex
    #
    vm
    wex
    #
    vx
    cio
    #
    c1
    cA
    chash
    cfv
    #
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    @20
    @28
    @3
    cF
    @30
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vx
    cio
    #
    cif
    #
    cif
    @0
    @1
    @2
    cH
    cplusg
    cfv
    #
    co
    #
    @2
    wceq
    #
    @2
    @1
    @40
    co
    #
    @2
    wceq
    #
    wa
    #
    vt
    cH
    cbs
    cfv
    #
    wral
    #
    vs
    @46
    crab
    #
    wss
    #
    cH
    c0g
    cfv
    #
    @15
    @19
    @20
    @17
    @40
    cF
    @16
    cseq
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @24
    wrex
    #
    vm
    wex
    #
    vx
    cio
    #
    c1
    cB
    chash
    cfv
    #
    cfz
    co
    #
    cB
    @30
    wf1o
    #
    @20
    @57
    @40
    @32
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vx
    cio
    #
    cif
    #
    cif
    cG
    cF
    cgsu
    co
    cH
    cF
    cgsu
    co
    wph
    @12
    @49
    @13
    @39
    @50
    @66
    wph
    @11
    @48
    @0
    wph
    @10
    @47
    vs
    @9
    @46
    gsumpropd2.b
    wph
    @1
    @9
    wcel
    #
    wa
    @8
    @45
    vt
    @9
    @46
    wph
    @9
    @46
    wceq
    @67
    gsumpropd2.b
    adantr
    wph
    @67
    @2
    @9
    wcel
    #
    @8
    @45
    wb
    wph
    @67
    @68
    wa
    #
    wa
    #
    @5
    @42
    @7
    @44
    @70
    @4
    @41
    @2
    gsumpropd2.e
    eqeq1d
    @70
    @6
    @43
    @2
    wph
    @68
    @67
    @6
    @43
    wceq
    wph
    va
    vb
    @9
    @9
    @3
    @40
    @2
    @1
    wph
    vs
    vt
    @9
    @9
    @3
    @40
    va
    cv
    #
    vb
    cv
    #
    gsumpropd2.e
    oveqrspc2v
    #
    oveqrspc2v
    ancom2s
    eqeq1d
    anbi12d
    anassrs
    raleqbidva
    rabeqbidva
    #
    sseq2d
    wph
    vs
    vt
    @9
    cG
    cH
    wph
    @9
    eqidd
    gsumpropd2.b
    gsumpropd2.e
    grpidpropd
    wph
    @15
    @27
    @56
    @38
    @65
    wph
    @26
    @55
    vx
    wph
    @25
    @54
    vm
    wph
    @23
    @53
    vn
    @24
    wph
    @17
    @24
    wcel
    #
    wa
    @19
    @22
    @52
    wph
    @75
    @19
    @22
    @52
    wb
    wph
    @75
    @19
    wa
    #
    wa
    #
    @21
    @51
    @20
    @77
    vs
    vt
    @3
    @40
    @9
    cF
    @16
    @17
    wph
    @75
    @19
    simprl
    @77
    @1
    @18
    wcel
    #
    wa
    #
    @0
    @9
    @1
    cF
    cfv
    #
    wph
    @0
    @9
    wss
    #
    @76
    @78
    gsumpropd2.r
    ad2antrr
    @79
    cF
    wfun
    #
    @1
    @14
    wcel
    @80
    @0
    wcel
    wph
    @82
    @76
    @78
    gsumpropd2.n
    ad2antrr
    @79
    @1
    @18
    @14
    @77
    @78
    simpr
    wph
    @75
    @19
    @78
    simplrr
    eleqtrrd
    @1
    cF
    fvelrn
    syl2anc
    sseldd
    wph
    @69
    @4
    @9
    wcel
    @76
    gsumpropd2.c
    adantlr
    wph
    @69
    @4
    @41
    wceq
    @76
    gsumpropd2.e
    adantlr
    seqfeq4
    eqeq2d
    anassrs
    pm5.32da
    rexbidva
    exbidv
    iotabidv
    wph
    @37
    @64
    vx
    wph
    @36
    @63
    vf
    wph
    @36
    @31
    @62
    wa
    @63
    wph
    @31
    @35
    @62
    wph
    @31
    wa
    #
    @34
    @61
    @20
    @83
    @34
    @57
    @33
    cfv
    #
    @61
    wph
    @34
    @84
    wceq
    @31
    wph
    @28
    @57
    @33
    wph
    cA
    cB
    chash
    wph
    cF
    ccnv
    #
    cvv
    @11
    cdif
    #
    cima
    #
    @85
    cvv
    @48
    cdif
    #
    cima
    #
    cA
    cB
    wph
    @86
    @88
    @85
    wph
    @11
    @48
    cvv
    @74
    difeq2d
    imaeq2d
    gsumprop2dlem.1
    gsumprop2dlem.2
    3eqtr4g
    #
    fveq2d
    #
    fveq2d
    adantr
    @83
    @57
    c1
    cuz
    cfv
    #
    wcel
    #
    @84
    @61
    wceq
    #
    @83
    @93
    wa
    #
    va
    vb
    @3
    @40
    @9
    @32
    c1
    @57
    @83
    @93
    simpr
    @95
    @71
    @58
    wcel
    #
    wa
    #
    @0
    @9
    @71
    @32
    cfv
    #
    wph
    @81
    @31
    @93
    @96
    gsumpropd2.r
    ad3antrrr
    @97
    @98
    @71
    @30
    cfv
    #
    cF
    cfv
    #
    @0
    @97
    @30
    wfun
    #
    @71
    @30
    cdm
    #
    wcel
    @98
    @100
    wceq
    @31
    @101
    wph
    @93
    @96
    @29
    cA
    @30
    f1ofun
    ad3antlr
    @97
    @71
    @58
    @102
    @95
    @96
    simpr
    #
    @97
    @102
    @29
    @58
    @31
    @102
    @29
    wceq
    wph
    @93
    @96
    @29
    cA
    @30
    f1odm
    ad3antlr
    wph
    @29
    @58
    wceq
    #
    @31
    @93
    @96
    wph
    @28
    @57
    c1
    cfz
    @91
    oveq2d
    #
    ad3antrrr
    #
    eqtrd
    eleqtrrd
    @71
    cF
    @30
    fvco
    syl2anc
    @97
    @82
    @99
    @14
    wcel
    @100
    @0
    wcel
    wph
    @82
    @31
    @93
    @96
    gsumpropd2.n
    ad3antrrr
    @97
    cA
    @14
    @99
    wph
    cA
    @14
    wss
    @31
    @93
    @96
    wph
    cA
    @85
    cvv
    cima
    #
    @14
    wph
    cA
    @107
    @85
    @11
    cima
    #
    cdif
    #
    @107
    wph
    cA
    @87
    @109
    gsumprop2dlem.1
    wph
    @82
    @87
    @109
    wceq
    gsumpropd2.n
    cvv
    @11
    cF
    difpreima
    syl
    syl5eq
    @107
    @108
    difss
    syl6eqss
    @14
    @85
    crn
    @107
    cF
    dfdm4
    @85
    dfrn4
    eqtri
    syl6sseqr
    ad3antrrr
    @97
    @29
    cA
    @71
    @30
    @31
    @29
    cA
    @30
    wf
    wph
    @93
    @96
    @29
    cA
    @30
    f1of
    ad3antlr
    @97
    @71
    @58
    @29
    @103
    @106
    eleqtrrd
    ffvelrnd
    sseldd
    @99
    cF
    fvelrn
    syl2anc
    eqeltrd
    sseldd
    @95
    wph
    @71
    @9
    wcel
    @72
    @9
    wcel
    wa
    #
    @71
    @72
    @3
    co
    #
    @9
    wcel
    wph
    @31
    @93
    simpll
    #
    wph
    vs
    vt
    @71
    @72
    @9
    @9
    @9
    @3
    gsumpropd2.c
    caovclg
    sylan
    @95
    wph
    @110
    @111
    @71
    @72
    @40
    co
    wceq
    @112
    @73
    sylan
    seqfeq4
    wph
    @93
    wn
    #
    @94
    @31
    wph
    @113
    wa
    #
    @84
    c0
    @61
    @114
    @57
    @33
    cdm
    #
    wcel
    #
    wn
    @84
    c0
    wceq
    @114
    @93
    @116
    wph
    @113
    simpr
    #
    @115
    @92
    @57
    c1
    cz
    wcel
    #
    @33
    @92
    wfn
    @115
    @92
    wceq
    1z
    @3
    @32
    c1
    seqfn
    @92
    @33
    fndm
    mp2b
    eleq2i
    sylnibr
    @57
    @33
    ndmfv
    syl
    @114
    @57
    @60
    cdm
    #
    wcel
    #
    wn
    @61
    c0
    wceq
    @114
    @93
    @120
    @117
    @119
    @92
    @57
    @118
    @60
    @92
    wfn
    @119
    @92
    wceq
    1z
    @40
    @32
    c1
    seqfn
    @92
    @60
    fndm
    mp2b
    eleq2i
    sylnibr
    @57
    @60
    ndmfv
    syl
    eqtr4d
    adantlr
    pm2.61dan
    eqtrd
    eqeq2d
    pm5.32da
    wph
    @31
    @59
    @62
    wph
    @31
    @58
    cA
    @30
    wf1o
    #
    @59
    wph
    @104
    @31
    @121
    wb
    @105
    @29
    @58
    cA
    @30
    f1oeq2
    syl
    wph
    cA
    cB
    wceq
    @121
    @59
    wb
    @90
    cA
    cB
    @58
    @30
    f1oeq3
    syl
    bitrd
    anbi1d
    bitrd
    exbidv
    iotabidv
    ifeq12d
    ifbieq12d
    wph
    vx
    vt
    @14
    @9
    @3
    vf
    vm
    vn
    cF
    cG
    @11
    cW
    cA
    cV
    @13
    vs
    @9
    eqid
    @13
    eqid
    @3
    eqid
    @11
    eqid
    cA
    @87
    wceq
    wph
    gsumprop2dlem.1
    a1i
    gsumpropd2.g
    gsumpropd2.f
    wph
    @14
    eqidd
    #
    gsumvalx
    wph
    vx
    vt
    @14
    @46
    @40
    vf
    vm
    vn
    cF
    cH
    @48
    cX
    cB
    cV
    @50
    vs
    @46
    eqid
    @50
    eqid
    @40
    eqid
    @48
    eqid
    cB
    @89
    wceq
    wph
    gsumprop2dlem.2
    a1i
    gsumpropd2.h
    gsumpropd2.f
    @122
    gsumvalx
    3eqtr4d
end
