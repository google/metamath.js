include "cr.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "citg2.mm"
include "cxr.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "wcel.mm"
include "wa.mm"
include "citg1.mm"
include "cdm.mm"
include "cmbf.mm"
include "ffvelrnda.mm"
include "i1fmbf.mm"
include "syl.mm"
include "wf.mm"
include "c0p.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "i1ff.mm"
include "c1.mm"
include "caddc.mm"
include "wral.mm"
include "breq2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "simpld.mm"
include "0plef.mm"
include "sylanbrc.mm"
include "simprd.mm"
include "wrex.mm"
include "rge0ssre.mm"
include "sseldi.mm"
include "itg2i1fseqle.mm"
include "cvv.mm"
include "wfn.mm"
include "ffn.mm"
include "adantr.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "itg2mono.mm"
include "feqmptd.mm"
include "cli.mm"
include "nnuz.mm"
include "1zzd.mm"
include "fmptd.mm"
include "peano2nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "3brtr4d.mm"
include "breq1d.mm"
include "ralbiia.mm"
include "rexbii.mm"
include "sylibr.mm"
include "climsup.mm"
include "climuni.mm"
include "syl5eqr.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "syl6eqr.mm"
include "itg2itg1.mm"
include "syl6reqr.mm"
include "3eqtr4d.mm"

theorem itg2i1fseq
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume itg2i1fseq.1: |- ( ph -> F e. MblFn )
  assume itg2i1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2i1fseq.3: |- ( ph -> P : NN --> dom S.1 )
  assume itg2i1fseq.4: |- ( ph -> A. n e. NN ( 0p oR <_ ( P ` n ) /\ ( P ` n ) oR <_ ( P ` ( n + 1 ) ) ) )
  assume itg2i1fseq.5: |- ( ph -> A. x e. RR ( n e. NN |-> ( ( P ` n ) ` x ) ) ~~> ( F ` x ) )
  assume itg2i1fseq.6: |- S = ( m e. NN |-> ( S.1 ` ( P ` m ) ) )

  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint m ph
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint M k
  disjoint M n
  disjoint M y
  disjoint M z
  disjoint P k
  disjoint P y
  disjoint P z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  disjoint S k
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( S.2 ` F ) = sup ( ran S , RR* , < ) )

  proof
    wph
    vx
    cr
    vn
    cn
    vx
    cv
    #
    vn
    cv
    #
    cP
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
    #
    citg2
    cfv
    vn
    cn
    @2
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
    cS
    crn
    #
    cxr
    clt
    csup
    wph
    vy
    vz
    @11
    vm
    cP
    @7
    vx
    vy
    cr
    @6
    vm
    cn
    vy
    cv
    #
    vm
    cv
    #
    cP
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
    @0
    @13
    wceq
    #
    cr
    @5
    @18
    clt
    @20
    @4
    @17
    @20
    @4
    vm
    cn
    @0
    @15
    cfv
    #
    cmpt
    @17
    vn
    vm
    cn
    @3
    @21
    @1
    @14
    wceq
    #
    @0
    @2
    @15
    @1
    @14
    cP
    fveq2
    #
    fveq1d
    cbvmptv
    @20
    vm
    cn
    @21
    @16
    @0
    @13
    @15
    fveq2
    mpteq2dv
    syl5eq
    rneqd
    supeq1d
    cbvmptv
    #
    wph
    @14
    cn
    wcel
    #
    wa
    #
    @15
    citg1
    cdm
    #
    wcel
    #
    @15
    cmbf
    wcel
    wph
    cn
    @27
    @14
    cP
    itg2i1fseq.3
    ffvelrnda
    #
    @15
    i1fmbf
    syl
    @26
    cr
    cr
    @15
    wf
    #
    c0p
    @15
    cle
    cofr
    #
    wbr
    #
    cr
    cc0
    cpnf
    cico
    co
    #
    @15
    wf
    @26
    @28
    @30
    @29
    @15
    i1ff
    syl
    #
    @26
    @32
    @15
    @14
    c1
    caddc
    co
    #
    cP
    cfv
    #
    @31
    wbr
    #
    wph
    c0p
    @2
    @31
    wbr
    #
    @2
    @1
    c1
    caddc
    co
    #
    cP
    cfv
    #
    @31
    wbr
    #
    wa
    #
    vn
    cn
    wral
    @25
    @32
    @37
    wa
    #
    itg2i1fseq.4
    @42
    @43
    vn
    @14
    cn
    @22
    @38
    @32
    @41
    @37
    @22
    @2
    @15
    c0p
    @31
    @23
    breq2d
    @22
    @2
    @15
    @40
    @36
    @31
    @23
    @22
    @39
    @35
    cP
    @1
    @14
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    anbi12d
    rspccva
    sylan
    #
    simpld
    #
    @15
    0plef
    sylanbrc
    @26
    @32
    @37
    @44
    simprd
    #
    wph
    @13
    cr
    wcel
    #
    wa
    #
    @13
    cF
    cfv
    #
    cr
    wcel
    @16
    @49
    cle
    wbr
    #
    vm
    cn
    wral
    #
    @16
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
    #
    @48
    @33
    cr
    @49
    rge0ssre
    wph
    cr
    @33
    @13
    cF
    itg2i1fseq.2
    ffvelrnda
    sseldi
    @48
    @50
    vm
    cn
    wph
    @25
    @47
    @50
    @26
    @50
    vy
    cr
    @26
    @15
    cF
    @31
    wbr
    @50
    vy
    cr
    wral
    wph
    vx
    cP
    vn
    cF
    @14
    itg2i1fseq.1
    itg2i1fseq.2
    itg2i1fseq.3
    itg2i1fseq.4
    itg2i1fseq.5
    itg2i1fseqle
    @26
    vy
    cr
    cr
    @16
    @49
    cle
    cr
    @15
    cF
    cvv
    cvv
    @26
    @30
    @15
    cr
    wfn
    @34
    cr
    cr
    @15
    ffn
    syl
    #
    wph
    cF
    cr
    wfn
    #
    @25
    wph
    cr
    @33
    cF
    wf
    @57
    itg2i1fseq.2
    cr
    @33
    cF
    ffn
    syl
    adantr
    cr
    cvv
    wcel
    @26
    reex
    a1i
    #
    @58
    cr
    inidm
    #
    @26
    @47
    wa
    #
    @16
    eqidd
    #
    @60
    @49
    eqidd
    ofrfval
    mpbid
    r19.21bi
    an32s
    ralrimiva
    @54
    @51
    vz
    @49
    cr
    @52
    @49
    wceq
    @53
    @50
    vm
    cn
    @52
    @49
    @16
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    cxr
    @10
    vm
    cn
    @15
    citg2
    cfv
    #
    cmpt
    #
    crn
    clt
    @9
    @64
    vn
    vm
    cn
    @8
    @63
    @22
    @2
    @15
    citg2
    @23
    fveq2d
    cbvmptv
    #
    rneqi
    supeq1i
    itg2mono
    wph
    cF
    @7
    citg2
    wph
    cF
    vy
    cr
    @19
    cmpt
    #
    @7
    wph
    cF
    vy
    cr
    @49
    cmpt
    @66
    wph
    vy
    cr
    @33
    cF
    itg2i1fseq.2
    feqmptd
    wph
    vy
    cr
    @19
    @49
    @48
    @19
    vn
    cn
    @13
    @2
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
    @49
    cr
    @69
    @18
    clt
    @68
    @17
    vn
    vm
    cn
    @67
    @16
    @22
    @13
    @2
    @15
    @23
    fveq1d
    #
    cbvmptv
    #
    rneqi
    supeq1i
    @48
    @68
    @70
    cli
    wbr
    @68
    @49
    cli
    wbr
    #
    @70
    @49
    wceq
    @48
    vz
    vm
    @68
    c1
    cn
    nnuz
    @48
    1zzd
    @48
    vm
    cn
    @16
    cr
    @68
    wph
    @25
    @47
    @16
    cr
    wcel
    @26
    cr
    cr
    @13
    @15
    @34
    ffvelrnda
    an32s
    @72
    fmptd
    @48
    @25
    wa
    @16
    @13
    @36
    cfv
    #
    @14
    @68
    cfv
    #
    @35
    @68
    cfv
    #
    cle
    wph
    @25
    @47
    @16
    @74
    cle
    wbr
    #
    @26
    @77
    vy
    cr
    @26
    @37
    @77
    vy
    cr
    wral
    @46
    @26
    vy
    cr
    cr
    @16
    @74
    cle
    cr
    @15
    @36
    cvv
    cvv
    @56
    @26
    cr
    cr
    @36
    wf
    #
    @36
    cr
    wfn
    @26
    @36
    @27
    wcel
    #
    @78
    wph
    cn
    @27
    cP
    wf
    @35
    cn
    wcel
    #
    @79
    @25
    itg2i1fseq.3
    @14
    peano2nn
    #
    cn
    @27
    @35
    cP
    ffvelrn
    syl2an
    @36
    i1ff
    syl
    cr
    cr
    @36
    ffn
    syl
    @58
    @58
    @59
    @61
    @60
    @74
    eqidd
    ofrfval
    mpbid
    r19.21bi
    an32s
    @25
    @75
    @16
    wceq
    @48
    vn
    @14
    @67
    @16
    cn
    @68
    @71
    @68
    eqid
    #
    @13
    @15
    fvex
    fvmpt
    #
    adantl
    @25
    @76
    @74
    wceq
    #
    @48
    @25
    @80
    @84
    @81
    vn
    @35
    @67
    @74
    cn
    @68
    @1
    @35
    wceq
    @13
    @2
    @36
    @1
    @35
    cP
    fveq2
    fveq1d
    @82
    @13
    @36
    fvex
    fvmpt
    syl
    adantl
    3brtr4d
    @48
    @55
    @75
    @52
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
    @62
    @86
    @54
    vz
    cr
    @85
    @53
    vm
    cn
    @25
    @75
    @16
    @52
    cle
    @83
    breq1d
    ralbiia
    rexbii
    sylibr
    climsup
    wph
    @4
    @0
    cF
    cfv
    #
    cli
    wbr
    #
    vx
    cr
    wral
    @47
    @73
    itg2i1fseq.5
    @88
    @73
    vx
    @13
    cr
    @20
    @4
    @68
    @87
    @49
    cli
    @20
    vn
    cn
    @3
    @67
    @0
    @13
    @2
    fveq2
    mpteq2dv
    @0
    @13
    cF
    fveq2
    breq12d
    rspccva
    sylan
    @70
    @49
    @68
    climuni
    syl2anc
    syl5eqr
    mpteq2dva
    eqtr4d
    @24
    syl6eqr
    fveq2d
    wph
    cxr
    @12
    @10
    clt
    wph
    cS
    @9
    wph
    cS
    @64
    @9
    wph
    @64
    vm
    cn
    @15
    citg1
    cfv
    #
    cmpt
    cS
    wph
    vm
    cn
    @63
    @89
    @26
    @28
    @32
    @63
    @89
    wceq
    @29
    @45
    @15
    itg2itg1
    syl2anc
    mpteq2dva
    itg2i1fseq.6
    syl6reqr
    @65
    syl6eqr
    rneqd
    supeq1d
    3eqtr4d
end
