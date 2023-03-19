include "clm.mm"
include "cfv.mm"
include "wrel.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "lmrel.mm"
include "cv.mm"
include "crrn.mm"
include "co.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "cr.mm"
include "cmap.mm"
include "wf.mm"
include "wfn.mm"
include "cmpt.mm"
include "cli.mm"
include "fvex.mm"
include "fnmpti.mm"
include "a1i.mm"
include "wa.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cvv.mm"
include "wceq.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fvmpt.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "syl6eleq.mm"
include "elmapi.mm"
include "syl.mm"
include "an32s.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "cmin.mm"
include "cabs.mm"
include "cca.mm"
include "cme.mm"
include "cxmt.mm"
include "cfn.mm"
include "rrnmet.mm"
include "metxmet.mm"
include "eqidd.mm"
include "iscauf.mm"
include "mpbid.mm"
include "adantr.mm"
include "cle.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "eluznn.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "simplr.mm"
include "rrndstprj1.mm"
include "syl22anc.mm"
include "metsym.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "adantllr.mm"
include "wi.mm"
include "remet.mm"
include "simpll.mm"
include "syl2anc.mm"
include "metcl.mm"
include "rpre.mm"
include "ad2antrr.mm"
include "lelttr.mm"
include "mpand.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "remetdval.mm"
include "ad2antlr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "sylibd.mm"
include "mpd.mm"
include "nnex.mm"
include "mptex.mm"
include "caucvg.mm"
include "climdm.mm"
include "sylib.mm"
include "mpteq2dv.mm"
include "breqtrrd.mm"
include "climrecl.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "wb.mm"
include "reex.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "syl6eleqr.mm"
include "c0.mm"
include "1nn.mm"
include "cc0.mm"
include "csqrt.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "adantlr.mm"
include "rrnmval.mm"
include "simplrr.mm"
include "sumeq1d.mm"
include "sum0.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "sqrt0.mm"
include "simplrl.mm"
include "rpgt0d.mm"
include "eqbrtrd.mm"
include "syl6eqr.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "expr.mm"
include "wne.mm"
include "chash.mm"
include "cdiv.mm"
include "cz.mm"
include "simprl.mm"
include "simprr.mm"
include "hashnncl.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rpdivcld.mm"
include "climi2.mm"
include "1z.mm"
include "rexuz3.mm"
include "ax-mp.mm"
include "sylan2.mm"
include "anassrs.mm"
include "syl5bbr.mm"
include "rexfiuz.mm"
include "syl5bb.mm"
include "cmul.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "w3a.mm"
include "rrndstprj2.mm"
include "syl31anc.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcan1d.mm"
include "breq2d.mm"
include "pm2.61dne.mm"
include "lmmbrf.mm"
include "mpbir2and.mm"
include "releldm.mm"

theorem rrncmslem
  let wph: wff ph
  let vt: setvar t
  let cP: class P
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let cX: class X
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume rrnval.1: |- X = ( RR ^m I )
  assume rrndstprj1.1: |- M = ( ( abs o. - ) |` ( RR X. RR ) )
  assume rrncms.3: |- J = ( MetOpen ` ( Rn ` I ) )
  assume rrncms.4: |- ( ph -> I e. Fin )
  assume rrncms.5: |- ( ph -> F e. ( Cau ` ( Rn ` I ) ) )
  assume rrncms.6: |- ( ph -> F : NN --> X )
  assume rrncms.7: |- P = ( m e. I |-> ( ~~> ` ( t e. NN |-> ( ( F ` t ) ` m ) ) ) )

  disjoint I m
  disjoint m t
  disjoint F m
  disjoint F t
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint G k
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint k m
  disjoint k z
  disjoint I k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n z
  disjoint I n
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint A k
  disjoint J x
  disjoint P j
  disjoint P k
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint R k
  disjoint R n
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint j t
  disjoint F j
  disjoint k t
  disjoint F k
  disjoint n t
  disjoint F n
  disjoint t x
  disjoint t y
  disjoint F x
  disjoint F y
  assert |- ( ph -> F e. dom ( ~~>t ` J ) )

  proof
    wph
    cJ
    clm
    cfv
    #
    wrel
    cF
    cP
    @0
    wbr
    #
    cF
    @0
    cdm
    wcel
    cJ
    lmrel
    wph
    @1
    cP
    cX
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    cP
    cI
    crrn
    cfv
    #
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    wph
    cP
    cr
    cI
    cmap
    co
    #
    cX
    wph
    cP
    @13
    wcel
    #
    cI
    cr
    cP
    wf
    #
    wph
    cP
    cI
    wfn
    #
    vn
    cv
    #
    cP
    cfv
    #
    cr
    wcel
    #
    vn
    cI
    wral
    @15
    @16
    wph
    vm
    cI
    vt
    cn
    vm
    cv
    #
    vt
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    cP
    @24
    cli
    fvex
    rrncms.7
    fnmpti
    a1i
    wph
    @19
    vn
    cI
    wph
    @17
    cI
    wcel
    #
    wa
    #
    @18
    vk
    vt
    cn
    @17
    @22
    cfv
    #
    cmpt
    #
    c1
    cn
    nnuz
    @27
    1zzd
    @27
    @29
    @29
    cli
    cfv
    #
    @18
    cli
    @27
    @29
    cli
    cdm
    wcel
    @29
    @30
    cli
    wbr
    @27
    vx
    vj
    vk
    @29
    c1
    cvv
    cn
    nnuz
    @27
    @3
    cn
    wcel
    #
    wa
    #
    @3
    @29
    cfv
    #
    @32
    @33
    @17
    @4
    cfv
    #
    cr
    @31
    @33
    @34
    wceq
    #
    @27
    vt
    @3
    @28
    @34
    cn
    @29
    vt
    vk
    weq
    @17
    @22
    @4
    @21
    @3
    cF
    fveq2
    fveq1d
    @29
    eqid
    #
    @17
    @4
    fvex
    fvmpt
    #
    adantl
    wph
    @31
    @26
    @34
    cr
    wcel
    #
    wph
    @31
    wa
    #
    cI
    cr
    @17
    @4
    @39
    @4
    @13
    wcel
    cI
    cr
    @4
    wf
    @39
    @4
    cX
    @13
    wph
    cn
    cX
    @3
    cF
    rrncms.6
    ffvelrnda
    #
    rrnval.1
    syl6eleq
    @4
    cr
    cI
    elmapi
    syl
    ffvelrnda
    an32s
    #
    eqeltrd
    #
    recnd
    @27
    @9
    cF
    cfv
    #
    @4
    @5
    co
    #
    @7
    clt
    wbr
    #
    vk
    @10
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    #
    @33
    @9
    @29
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    vk
    @10
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    #
    wph
    @48
    @26
    wph
    cF
    @5
    cca
    cfv
    wcel
    @48
    rrncms.5
    wph
    vx
    @4
    @43
    @5
    vj
    vk
    cF
    c1
    cX
    cn
    nnuz
    wph
    @5
    cX
    cme
    cfv
    wcel
    #
    @5
    cX
    cxmt
    cfv
    wcel
    wph
    cI
    cfn
    wcel
    #
    @56
    rrncms.4
    cI
    cX
    rrnval.1
    rrnmet
    syl
    #
    @5
    cX
    metxmet
    syl
    #
    wph
    1zzd
    #
    @39
    @4
    eqidd
    #
    wph
    @9
    cn
    wcel
    #
    wa
    #
    @43
    eqidd
    rrncms.6
    iscauf
    mpbid
    adantr
    @27
    @48
    @34
    @17
    @43
    cfv
    #
    cM
    co
    #
    @7
    clt
    wbr
    #
    vk
    @10
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    @55
    @27
    @47
    @68
    vx
    crp
    @27
    @7
    crp
    wcel
    #
    wa
    #
    @46
    @67
    vj
    cn
    @70
    @62
    wa
    #
    @45
    @66
    vk
    @10
    @71
    @3
    @10
    wcel
    #
    wa
    #
    @65
    @44
    cle
    wbr
    #
    @45
    @66
    @27
    @62
    @72
    @74
    @69
    @27
    @62
    wa
    #
    @72
    wa
    #
    @65
    @4
    @43
    @5
    co
    #
    @44
    cle
    @76
    @57
    @26
    @4
    cX
    wcel
    #
    @43
    cX
    wcel
    #
    @65
    @77
    cle
    wbr
    wph
    @57
    @26
    @62
    @72
    rrncms.4
    ad3antrrr
    wph
    @26
    @62
    @72
    simpllr
    @76
    cn
    cX
    @3
    cF
    wph
    cn
    cX
    cF
    wf
    #
    @26
    @62
    @72
    rrncms.6
    ad3antrrr
    #
    @62
    @72
    @31
    @27
    @3
    @9
    eluznn
    #
    adantll
    #
    ffvelrnd
    #
    @76
    cn
    cX
    @9
    cF
    @81
    @27
    @62
    @72
    simplr
    ffvelrnd
    #
    @17
    @4
    @43
    cI
    cM
    cX
    rrnval.1
    rrndstprj1.1
    rrndstprj1
    syl22anc
    @76
    @56
    @78
    @79
    @77
    @44
    wceq
    wph
    @56
    @26
    @62
    @72
    @58
    ad3antrrr
    #
    @84
    @85
    @4
    @43
    @5
    cX
    metsym
    syl3anc
    breqtrd
    adantllr
    @73
    @65
    cr
    wcel
    #
    @44
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @74
    @45
    wa
    @66
    wi
    @27
    @62
    @72
    @87
    @69
    @76
    cM
    cr
    cme
    cfv
    wcel
    #
    @38
    @64
    cr
    wcel
    #
    @87
    @90
    @76
    cM
    rrndstprj1.1
    remet
    a1i
    @76
    @27
    @31
    @38
    @27
    @62
    @72
    simpll
    @83
    @41
    syl2anc
    #
    @75
    @91
    @72
    wph
    @62
    @26
    @91
    @63
    cI
    cr
    @17
    @43
    @63
    @43
    @13
    wcel
    cI
    cr
    @43
    wf
    @63
    @43
    cX
    @13
    wph
    cn
    cX
    @9
    cF
    rrncms.6
    ffvelrnda
    rrnval.1
    syl6eleq
    @43
    cr
    cI
    elmapi
    syl
    ffvelrnda
    an32s
    adantr
    #
    @34
    @64
    cM
    cr
    metcl
    syl3anc
    adantllr
    @27
    @62
    @72
    @88
    @69
    @76
    @56
    @79
    @78
    @88
    @86
    @85
    @84
    @43
    @4
    @5
    cX
    metcl
    syl3anc
    adantllr
    @70
    @89
    @62
    @72
    @69
    @89
    @27
    @7
    rpre
    adantl
    ad2antrr
    @65
    @44
    @7
    lelttr
    syl3anc
    mpand
    ralimdva
    reximdva
    ralimdva
    @27
    @68
    @54
    vx
    crp
    @27
    @67
    @53
    vj
    cn
    @75
    @66
    @52
    vk
    @10
    @76
    @65
    @51
    @7
    clt
    @76
    @65
    @34
    @64
    cmin
    co
    #
    cabs
    cfv
    #
    @51
    @76
    @38
    @91
    @65
    @95
    wceq
    @92
    @93
    @34
    @64
    cM
    rrndstprj1.1
    remetdval
    syl2anc
    @76
    @50
    @94
    cabs
    @76
    @33
    @34
    @49
    @64
    cmin
    @76
    @31
    @35
    @83
    @37
    syl
    @62
    @49
    @64
    wceq
    @27
    @72
    vt
    @9
    @28
    @64
    cn
    @29
    vt
    vj
    weq
    @17
    @22
    @43
    @21
    @9
    cF
    fveq2
    fveq1d
    @36
    @17
    @43
    fvex
    fvmpt
    ad2antlr
    oveq12d
    fveq2d
    eqtr4d
    breq1d
    ralbidva
    rexbidva
    ralbidv
    sylibd
    mpd
    @29
    cvv
    wcel
    @27
    vt
    cn
    @28
    nnex
    mptex
    a1i
    caucvg
    @29
    climdm
    sylib
    @26
    @18
    @30
    wceq
    wph
    vm
    @17
    @25
    @30
    cI
    cP
    vm
    vn
    weq
    #
    @24
    @29
    cli
    @96
    vt
    cn
    @23
    @28
    @20
    @17
    @22
    fveq2
    mpteq2dv
    fveq2d
    rrncms.7
    @29
    cli
    fvex
    fvmpt
    adantl
    breqtrrd
    #
    @42
    climrecl
    #
    ralrimiva
    vn
    cI
    cr
    cP
    ffnfv
    sylanbrc
    wph
    cr
    cvv
    wcel
    @57
    @14
    @15
    wb
    reex
    rrncms.4
    cr
    cI
    cP
    cvv
    cfn
    elmapg
    sylancr
    mpbird
    rrnval.1
    syl6eleqr
    #
    wph
    @12
    vx
    crp
    wph
    @69
    wa
    @12
    cI
    c0
    wph
    @69
    cI
    c0
    wceq
    #
    @12
    wph
    @69
    @100
    wa
    #
    wa
    #
    c1
    cn
    wcel
    @8
    vk
    cn
    wral
    #
    @12
    1nn
    @102
    @8
    vk
    cn
    @102
    @31
    wa
    #
    @6
    cc0
    @7
    clt
    @104
    @6
    cc0
    csqrt
    cfv
    #
    cc0
    @104
    @6
    cI
    vy
    cv
    #
    @4
    cfv
    @106
    cP
    cfv
    cmin
    co
    c2
    cexp
    co
    #
    vy
    csu
    #
    csqrt
    cfv
    #
    @105
    @104
    @57
    @78
    @2
    @6
    @109
    wceq
    wph
    @57
    @101
    @31
    rrncms.4
    ad2antrr
    wph
    @31
    @78
    @101
    @40
    adantlr
    wph
    @2
    @101
    @31
    @99
    ad2antrr
    vy
    @4
    cP
    cI
    cX
    rrnval.1
    rrnmval
    syl3anc
    @104
    @108
    cc0
    csqrt
    @104
    @108
    c0
    @107
    vy
    csu
    cc0
    @104
    cI
    c0
    @107
    vy
    wph
    @69
    @100
    @31
    simplrr
    sumeq1d
    @107
    vy
    sum0
    syl6eq
    fveq2d
    eqtrd
    sqrt0
    syl6eq
    @104
    @7
    wph
    @69
    @100
    @31
    simplrl
    rpgt0d
    eqbrtrd
    ralrimiva
    @11
    @103
    vj
    c1
    cn
    @9
    c1
    wceq
    #
    @8
    vk
    @10
    cn
    @110
    @10
    c1
    cuz
    cfv
    cn
    @9
    c1
    cuz
    fveq2
    nnuz
    syl6eqr
    raleqdv
    rspcev
    sylancr
    expr
    wph
    @69
    cI
    c0
    wne
    #
    @12
    wph
    @69
    @111
    wa
    #
    wa
    #
    @34
    @18
    cM
    co
    #
    @7
    cI
    chash
    cfv
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vn
    cI
    wral
    #
    vk
    @10
    wral
    #
    vj
    cn
    wrex
    #
    @12
    @113
    @121
    @118
    vk
    @10
    wral
    #
    vj
    cz
    wrex
    #
    vn
    cI
    wral
    #
    @113
    @123
    vn
    cI
    @113
    @26
    wa
    #
    @123
    @34
    @18
    cmin
    co
    cabs
    cfv
    #
    @117
    clt
    wbr
    #
    vk
    @10
    wral
    #
    vj
    cn
    wrex
    #
    @125
    @18
    @34
    @117
    vj
    vk
    @29
    c1
    cn
    nnuz
    @125
    1zzd
    @113
    @117
    crp
    wcel
    #
    @26
    @113
    @7
    @116
    wph
    @69
    @111
    simprl
    @113
    @115
    @113
    @115
    @113
    @115
    cn
    wcel
    #
    @111
    wph
    @69
    @111
    simprr
    @113
    @57
    @131
    @111
    wb
    wph
    @57
    @112
    rrncms.4
    adantr
    #
    cI
    hashnncl
    syl
    mpbird
    nnrpd
    rpsqrtcld
    #
    rpdivcld
    #
    adantr
    @31
    @35
    @125
    @37
    adantl
    wph
    @26
    @29
    @18
    cli
    wbr
    @112
    @97
    adantlr
    climi2
    @123
    @122
    vj
    cn
    wrex
    #
    @125
    @129
    c1
    cz
    wcel
    #
    @135
    @123
    wb
    1z
    @118
    vj
    vk
    c1
    cn
    nnuz
    rexuz3
    ax-mp
    @125
    @122
    @128
    vj
    cn
    @125
    @62
    wa
    @118
    @127
    vk
    @10
    @125
    @62
    @72
    @118
    @127
    wb
    #
    @62
    @72
    wa
    #
    @125
    @31
    @137
    @82
    @125
    @31
    wa
    #
    @114
    @126
    @117
    clt
    @139
    @38
    @19
    @114
    @126
    wceq
    wph
    @26
    @31
    @38
    @112
    @41
    adantllr
    @125
    @19
    @31
    wph
    @26
    @19
    @112
    @98
    adantlr
    adantr
    @34
    @18
    cM
    rrndstprj1.1
    remetdval
    syl2anc
    breq1d
    sylan2
    anassrs
    ralbidva
    rexbidva
    syl5bbr
    mpbird
    ralrimiva
    @121
    @120
    vj
    cz
    wrex
    #
    @113
    @124
    @136
    @121
    @140
    wb
    1z
    @119
    vj
    vk
    c1
    cn
    nnuz
    rexuz3
    ax-mp
    @113
    @57
    @140
    @124
    wb
    @132
    @118
    cI
    vj
    vk
    vn
    rexfiuz
    syl
    syl5bb
    mpbird
    @113
    @120
    @11
    vj
    cn
    @113
    @62
    wa
    @119
    @8
    vk
    @10
    @113
    @62
    @72
    @119
    @8
    wi
    #
    @138
    @113
    @31
    @141
    @82
    @113
    @31
    wa
    #
    @119
    @6
    @117
    @116
    cmul
    co
    #
    clt
    wbr
    #
    @8
    @142
    cI
    cfn
    c0
    csn
    cdif
    wcel
    #
    @78
    @2
    @130
    @119
    @144
    wi
    @142
    @57
    @111
    @145
    wph
    @57
    @112
    @31
    rrncms.4
    ad2antrr
    wph
    @69
    @111
    @31
    simplrr
    cI
    cfn
    c0
    eldifsn
    sylanbrc
    @113
    cn
    cX
    @3
    cF
    wph
    @80
    @112
    rrncms.6
    adantr
    ffvelrnda
    wph
    @2
    @112
    @31
    @99
    ad2antrr
    @113
    @130
    @31
    @134
    adantr
    @145
    @78
    @2
    w3a
    @130
    @119
    @144
    @117
    vn
    @4
    cP
    cI
    cM
    cX
    rrnval.1
    rrndstprj1.1
    rrndstprj2
    expr
    syl31anc
    @142
    @143
    @7
    @6
    clt
    @142
    @7
    @116
    @142
    @7
    wph
    @69
    @111
    @31
    simplrl
    rpcnd
    @142
    @116
    @113
    @116
    crp
    wcel
    @31
    @133
    adantr
    #
    rpcnd
    @142
    @116
    @146
    rpne0d
    divcan1d
    breq2d
    sylibd
    sylan2
    anassrs
    ralimdva
    reximdva
    mpd
    expr
    pm2.61dne
    ralrimiva
    wph
    vx
    @4
    @5
    cP
    vj
    vk
    cF
    cJ
    c1
    cX
    cn
    rrncms.3
    @59
    nnuz
    @60
    @61
    rrncms.6
    lmmbrf
    mpbir2and
    cF
    cP
    @0
    releldm
    sylancr
end
