include "citg2.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cofr.mm"
include "citg1.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "cn.mm"
include "cmbf.mm"
include "adantlr.mm"
include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "wrex.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprr.mm"
include "itg2monolem3.mm"
include "expr.mm"
include "pm2.18d.mm"
include "ralrimiva.mm"
include "cicc.mm"
include "cxr.mm"
include "wb.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"
include "ffvelrnda.mm"
include "an32s.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "1nn.mm"
include "dmmptd.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "wfn.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "breq1d.mm"
include "ralbiia.mm"
include "cbvralv.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "rexrd.mm"
include "0red.mm"
include "feq1d.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "elrege0.mm"
include "simpld.mm"
include "simprd.mm"
include "ax-mp.mm"
include "fnfvelrn.mm"
include "syl5eqelr.mm"
include "suprub.mm"
include "syl31anc.mm"
include "letrd.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "icossicc.mm"
include "itg2cl.mm"
include "supxrcl.mm"
include "syl5eqel.mm"
include "itg2leub.mm"
include "syl2anc.mm"
include "r19.21bi.mm"
include "adantr.mm"
include "w3a.mm"
include "3jca.mm"
include "ad2antlr.mm"
include "simplr.mm"
include "eqeltrrd.mm"
include "cvv.mm"
include "simpr.mm"
include "ltso.mm"
include "supex.mm"
include "fvmpt2.mm"
include "breqtrrd.mm"
include "breq12d.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "itg2le.mm"
include "fveq2d.mm"
include "supxrleub.mm"
include "syl5eqbr.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem itg2mono
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  let cA: class A
  let vf: setvar f
  let vm: setvar m
  let vt: setvar t
  let vz: setvar z
  let vw: setvar w
  let cH: class H
  let cP: class P
  let cT: class T
  assume itg2mono.1: |- G = ( x e. RR |-> sup ( ran ( n e. NN |-> ( ( F ` n ) ` x ) ) , RR , < ) )
  assume itg2mono.2: |- ( ( ph /\ n e. NN ) -> ( F ` n ) e. MblFn )
  assume itg2mono.3: |- ( ( ph /\ n e. NN ) -> ( F ` n ) : RR --> ( 0 [,) +oo ) )
  assume itg2mono.4: |- ( ( ph /\ n e. NN ) -> ( F ` n ) oR <_ ( F ` ( n + 1 ) ) )
  assume itg2mono.5: |- ( ( ph /\ x e. RR ) -> E. y e. RR A. n e. NN ( ( F ` n ) ` x ) <_ y )
  assume itg2mono.6: |- S = sup ( ran ( n e. NN |-> ( S.2 ` ( F ` n ) ) ) , RR* , < )

  disjoint n x
  disjoint n y
  disjoint G n
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint m n
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n t
  disjoint n z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint j n
  disjoint j w
  disjoint j y
  disjoint H j
  disjoint k n
  disjoint k w
  disjoint k y
  disjoint H k
  disjoint n w
  disjoint H n
  disjoint w x
  disjoint w y
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint P n
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint j m
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k z
  disjoint F k
  disjoint m w
  disjoint F m
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint f j
  disjoint f k
  disjoint f w
  disjoint f ph
  disjoint j t
  disjoint j ph
  disjoint k t
  disjoint k ph
  disjoint m ph
  disjoint t w
  disjoint ph t
  disjoint ph w
  disjoint ph z
  disjoint S f
  disjoint S k
  disjoint S t
  disjoint T j
  disjoint T k
  disjoint T n
  disjoint T w
  disjoint T x
  disjoint T y
  assert |- ( ph -> ( S.2 ` G ) = S )

  proof
    wph
    cG
    citg2
    cfv
    #
    cS
    wceq
    #
    @0
    cS
    cle
    wbr
    #
    cS
    @0
    cle
    wbr
    #
    wph
    @2
    vf
    cv
    #
    cG
    cle
    cofr
    #
    wbr
    #
    @4
    citg1
    cfv
    cS
    cle
    wbr
    #
    wi
    #
    vf
    citg1
    cdm
    #
    wral
    #
    wph
    @8
    vf
    @9
    wph
    @4
    @9
    wcel
    #
    @6
    @7
    wph
    @11
    @6
    wa
    #
    wa
    @7
    wph
    @12
    @7
    wn
    #
    @7
    wph
    @12
    @13
    wa
    #
    wa
    vx
    vy
    @4
    cS
    vn
    cF
    cG
    itg2mono.1
    wph
    vn
    cv
    #
    cn
    wcel
    #
    @15
    cF
    cfv
    #
    cmbf
    wcel
    @14
    itg2mono.2
    adantlr
    wph
    @16
    cr
    cc0
    cpnf
    cico
    co
    #
    @17
    wf
    #
    @14
    itg2mono.3
    adantlr
    wph
    @16
    @17
    @15
    c1
    caddc
    co
    cF
    cfv
    @5
    wbr
    @14
    itg2mono.4
    adantlr
    wph
    vx
    cv
    #
    cr
    wcel
    #
    @20
    @17
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vn
    cn
    wral
    #
    vy
    cr
    wrex
    #
    @14
    itg2mono.5
    adantlr
    itg2mono.6
    wph
    @11
    @6
    @13
    simprll
    wph
    @11
    @6
    @13
    simprlr
    wph
    @12
    @13
    simprr
    itg2monolem3
    expr
    pm2.18d
    expr
    ralrimiva
    wph
    cr
    cc0
    cpnf
    cicc
    co
    #
    cG
    wf
    #
    cS
    cxr
    wcel
    #
    @2
    @10
    wb
    wph
    vx
    cr
    vn
    cn
    @22
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    @27
    cG
    wph
    @21
    wa
    #
    @32
    cxr
    wcel
    cc0
    @32
    cle
    wbr
    @32
    @27
    wcel
    @33
    @32
    @33
    @31
    cr
    wss
    #
    @31
    c0
    wne
    #
    vz
    cv
    #
    @23
    cle
    wbr
    #
    vz
    @31
    wral
    #
    vy
    cr
    wrex
    #
    @32
    cr
    wcel
    @33
    cn
    cr
    @30
    wf
    #
    @34
    @33
    vn
    cn
    @22
    cr
    @30
    wph
    @16
    @21
    @22
    cr
    wcel
    wph
    @16
    wa
    #
    cr
    cr
    @20
    @17
    @41
    @19
    @18
    cr
    wss
    cr
    cr
    @17
    wf
    itg2mono.3
    rge0ssre
    cr
    @18
    cr
    @17
    fss
    sylancl
    ffvelrnda
    an32s
    #
    @30
    eqid
    #
    fmptd
    #
    cn
    cr
    @30
    frn
    syl
    #
    @33
    @30
    cdm
    #
    c0
    wne
    #
    @35
    @33
    c1
    @46
    wcel
    @47
    @33
    c1
    cn
    @46
    1nn
    @33
    vn
    @30
    cn
    @22
    cr
    @43
    @42
    dmmptd
    syl5eleqr
    @46
    c1
    ne0i
    syl
    @46
    c0
    @31
    c0
    @30
    dm0rn0
    necon3bii
    sylib
    #
    @33
    @39
    @26
    itg2mono.5
    @33
    @38
    @25
    vy
    cr
    @33
    @38
    vm
    cv
    #
    @30
    cfv
    #
    @23
    cle
    wbr
    #
    vm
    cn
    wral
    #
    @25
    @33
    @30
    cn
    wfn
    #
    @38
    @52
    wb
    @33
    @40
    @53
    @44
    cn
    cr
    @30
    ffn
    syl
    #
    @37
    @51
    vz
    vm
    cn
    @30
    @36
    @50
    @23
    cle
    breq1
    ralrn
    syl
    @52
    @20
    @49
    cF
    cfv
    #
    cfv
    #
    @23
    cle
    wbr
    #
    vm
    cn
    wral
    @25
    @51
    @57
    vm
    cn
    @49
    cn
    wcel
    #
    @50
    @56
    @23
    cle
    vn
    @49
    @22
    @56
    cn
    @30
    vn
    vm
    weq
    #
    @20
    @17
    @55
    @15
    @49
    cF
    fveq2
    #
    fveq1d
    #
    @43
    @20
    @55
    fvex
    fvmpt
    #
    breq1d
    ralbiia
    @24
    @57
    vn
    vm
    cn
    @59
    @22
    @56
    @23
    cle
    @61
    breq1d
    cbvralv
    bitr4i
    syl6bb
    rexbidv
    mpbird
    #
    vy
    vz
    @31
    suprcl
    syl3anc
    #
    rexrd
    @33
    cc0
    @20
    c1
    cF
    cfv
    #
    cfv
    #
    @32
    @33
    0red
    @33
    @66
    cr
    wcel
    #
    cc0
    @66
    cle
    wbr
    #
    @33
    @66
    @18
    wcel
    @67
    @68
    wa
    wph
    cr
    @18
    @20
    @65
    c1
    cn
    wcel
    #
    wph
    @19
    vn
    cn
    wral
    #
    cr
    @18
    @65
    wf
    #
    1nn
    wph
    @19
    vn
    cn
    itg2mono.3
    ralrimiva
    #
    @19
    @71
    vn
    c1
    cn
    @15
    c1
    wceq
    #
    cr
    @18
    @17
    @65
    @15
    c1
    cF
    fveq2
    #
    feq1d
    rspcv
    mpsyl
    ffvelrnda
    @66
    elrege0
    sylib
    #
    simpld
    @64
    @33
    @67
    @68
    @75
    simprd
    @33
    @34
    @35
    @39
    @66
    @31
    wcel
    @66
    @32
    cle
    wbr
    @45
    @48
    @63
    @33
    @66
    c1
    @30
    cfv
    #
    @31
    @69
    @76
    @66
    wceq
    1nn
    vn
    c1
    @22
    @66
    cn
    @30
    @73
    @20
    @17
    @65
    @74
    fveq1d
    @43
    @20
    @65
    fvex
    fvmpt
    ax-mp
    @33
    @53
    @69
    @76
    @31
    wcel
    @54
    1nn
    cn
    c1
    @30
    fnfvelrn
    sylancl
    syl5eqelr
    vy
    vz
    @31
    @66
    suprub
    syl31anc
    letrd
    @32
    elxrge0
    sylanbrc
    itg2mono.1
    fmptd
    #
    wph
    cS
    vn
    cn
    @17
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
    cxr
    itg2mono.6
    wph
    @80
    cxr
    wss
    #
    @81
    cxr
    wcel
    wph
    cn
    cxr
    @79
    wf
    #
    @82
    wph
    vn
    cn
    @78
    cxr
    @79
    @41
    cr
    @27
    @17
    wf
    #
    @78
    cxr
    wcel
    @41
    @19
    @18
    @27
    wss
    #
    @84
    itg2mono.3
    cc0
    cpnf
    icossicc
    #
    cr
    @18
    @27
    @17
    fss
    sylancl
    @17
    itg2cl
    syl
    @79
    eqid
    #
    fmptd
    #
    cn
    cxr
    @79
    frn
    syl
    #
    @80
    supxrcl
    syl
    syl5eqel
    #
    cS
    vf
    cG
    itg2leub
    syl2anc
    mpbird
    wph
    cS
    @81
    @0
    cle
    itg2mono.6
    wph
    @81
    @0
    cle
    wbr
    #
    @36
    @0
    cle
    wbr
    #
    vz
    @80
    wral
    #
    wph
    @93
    @55
    citg2
    cfv
    #
    @0
    cle
    wbr
    #
    vm
    cn
    wral
    #
    wph
    @95
    vm
    cn
    wph
    @58
    wa
    #
    cr
    @27
    @55
    wf
    #
    @28
    @55
    cG
    @5
    wbr
    #
    @95
    @97
    cr
    @18
    @55
    wf
    #
    @85
    @98
    wph
    @100
    vm
    cn
    wph
    @70
    @100
    vm
    cn
    wral
    @72
    @19
    @100
    vn
    vm
    cn
    @59
    cr
    @18
    @17
    @55
    @60
    feq1d
    cbvralv
    sylib
    r19.21bi
    @86
    cr
    @18
    @27
    @55
    fss
    sylancl
    #
    wph
    @28
    @58
    @77
    adantr
    @97
    @99
    @36
    @55
    cfv
    #
    @36
    cG
    cfv
    #
    cle
    wbr
    #
    vz
    cr
    wral
    #
    @97
    @56
    @20
    cG
    cfv
    #
    cle
    wbr
    #
    vx
    cr
    wral
    @105
    @97
    @107
    vx
    cr
    @97
    @21
    wa
    #
    @56
    @32
    @106
    cle
    @108
    @34
    @35
    @39
    w3a
    #
    @56
    @31
    wcel
    @56
    @32
    cle
    wbr
    wph
    @21
    @109
    @58
    @33
    @34
    @35
    @39
    @45
    @48
    @63
    3jca
    adantlr
    @108
    @50
    @56
    @31
    @58
    @50
    @56
    wceq
    wph
    @21
    @62
    ad2antlr
    @108
    @53
    @58
    @50
    @31
    wcel
    wph
    @21
    @53
    @58
    @54
    adantlr
    wph
    @58
    @21
    simplr
    cn
    @49
    @30
    fnfvelrn
    syl2anc
    eqeltrrd
    vy
    vz
    @31
    @56
    suprub
    syl2anc
    @108
    @21
    @32
    cvv
    wcel
    @106
    @32
    wceq
    @97
    @21
    simpr
    cr
    @31
    clt
    ltso
    supex
    vx
    cr
    @32
    cvv
    cG
    itg2mono.1
    fvmpt2
    sylancl
    breqtrrd
    ralrimiva
    @107
    @104
    vx
    vz
    cr
    vx
    vz
    weq
    @56
    @102
    @106
    @103
    cle
    @20
    @36
    @55
    fveq2
    @20
    @36
    cG
    fveq2
    breq12d
    cbvralv
    sylib
    @97
    vz
    cr
    cr
    @102
    @103
    cle
    cr
    @55
    cG
    cvv
    cvv
    @97
    @98
    @55
    cr
    wfn
    @101
    cr
    @27
    @55
    ffn
    syl
    wph
    cG
    cr
    wfn
    #
    @58
    wph
    cr
    cr
    cG
    wf
    @110
    wph
    vx
    cr
    @32
    cr
    cG
    @64
    itg2mono.1
    fmptd
    cr
    cr
    cG
    ffn
    syl
    adantr
    cr
    cvv
    wcel
    @97
    reex
    a1i
    #
    @111
    cr
    inidm
    @97
    @36
    cr
    wcel
    wa
    #
    @102
    eqidd
    @112
    @103
    eqidd
    ofrfval
    mpbird
    @55
    cG
    itg2le
    syl3anc
    ralrimiva
    wph
    @93
    @49
    @79
    cfv
    #
    @0
    cle
    wbr
    #
    vm
    cn
    wral
    #
    @96
    wph
    @79
    cn
    wfn
    #
    @93
    @115
    wb
    wph
    @83
    @116
    @88
    cn
    cxr
    @79
    ffn
    syl
    @92
    @114
    vz
    vm
    cn
    @79
    @36
    @113
    @0
    cle
    breq1
    ralrn
    syl
    @114
    @95
    vm
    cn
    @58
    @113
    @94
    @0
    cle
    vn
    @49
    @78
    @94
    cn
    @79
    @59
    @17
    @55
    citg2
    @60
    fveq2d
    @87
    @55
    citg2
    fvex
    fvmpt
    breq1d
    ralbiia
    syl6bb
    mpbird
    wph
    @82
    @0
    cxr
    wcel
    #
    @91
    @93
    wb
    @89
    wph
    @28
    @117
    @77
    cG
    itg2cl
    syl
    #
    vz
    @80
    @0
    supxrleub
    syl2anc
    mpbird
    syl5eqbr
    wph
    @117
    @29
    @1
    @2
    @3
    wa
    wb
    @118
    @90
    @0
    cS
    xrletri3
    syl2anc
    mpbir2and
end
