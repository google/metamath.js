include "c0.mm"
include "wceq.mm"
include "cdiv.mm"
include "co.mm"
include "cprod.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "1div1e1.mm"
include "eqcomi.mm"
include "prodeq1.mm"
include "prod0.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "3eqtr4a.mm"
include "a1i.mm"
include "cmpt.mm"
include "cmul.mm"
include "ccom.mm"
include "cseq.mm"
include "cuz.mm"
include "simprl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "cc.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "f1of.mm"
include "adantl.mm"
include "fco.mm"
include "syl2an.mm"
include "ffvelrnda.mm"
include "cc0.mm"
include "simprr.mm"
include "syl.mm"
include "fvco3.mm"
include "sylan.mm"
include "wne.mm"
include "wral.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqnetrd.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfne.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "divcld.mm"
include "eqtr4d.mm"
include "nfov.mm"
include "nfeq.mm"
include "eqeq12d.mm"
include "3eqtr4d.mm"
include "prodfdiv.mm"
include "adantr.mm"
include "fprod.mm"
include "prodfc.mm"
include "oveq12i.mm"
include "3eqtr3g.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fproddiv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assume fprodmul.1: |- ( ph -> A e. Fin )
  assume fprodmul.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodmul.3: |- ( ( ph /\ k e. A ) -> C e. CC )
  assume fproddiv.4: |- ( ( ph /\ k e. A ) -> C =/= 0 )

  disjoint A k
  disjoint k ph
  disjoint A f
  disjoint A m
  disjoint B f
  disjoint B m
  disjoint C f
  disjoint C m
  disjoint f k
  disjoint f ph
  disjoint k m
  disjoint A n
  disjoint B n
  disjoint C n
  disjoint f m
  disjoint f n
  disjoint k n
  disjoint m n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> prod_ k e. A ( B / C ) = ( prod_ k e. A B / prod_ k e. A C ) )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cB
    cC
    cdiv
    co
    #
    vk
    cprod
    #
    cA
    cB
    vk
    cprod
    #
    cA
    cC
    vk
    cprod
    #
    cdiv
    co
    #
    wceq
    #
    cA
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @7
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    @0
    @6
    wi
    wph
    @0
    c1
    c1
    c1
    cdiv
    co
    #
    @2
    @5
    @14
    c1
    1div1e1
    eqcomi
    @0
    @2
    c0
    @1
    vk
    cprod
    c1
    cA
    c0
    @1
    vk
    prodeq1
    @1
    vk
    prod0
    syl6eq
    @0
    @3
    c1
    @4
    c1
    cdiv
    @0
    @3
    c0
    cB
    vk
    cprod
    c1
    cA
    c0
    cB
    vk
    prodeq1
    cB
    vk
    prod0
    syl6eq
    @0
    @4
    c0
    cC
    vk
    cprod
    c1
    cA
    c0
    cC
    vk
    prodeq1
    cC
    vk
    prod0
    syl6eq
    oveq12d
    3eqtr4a
    a1i
    wph
    @8
    @12
    @6
    wph
    @8
    wa
    @11
    @6
    vf
    wph
    @8
    @11
    @6
    wph
    @8
    @11
    wa
    #
    wa
    #
    cA
    vm
    cv
    #
    vk
    cA
    @1
    cmpt
    #
    cfv
    #
    vm
    cprod
    #
    cA
    @17
    vk
    cA
    cB
    cmpt
    #
    cfv
    #
    vm
    cprod
    #
    cA
    @17
    vk
    cA
    cC
    cmpt
    #
    cfv
    #
    vm
    cprod
    #
    cdiv
    co
    #
    @2
    @5
    @16
    @7
    cmul
    @18
    @10
    ccom
    #
    c1
    cseq
    cfv
    @7
    cmul
    @21
    @10
    ccom
    #
    c1
    cseq
    cfv
    #
    @7
    cmul
    @24
    @10
    ccom
    #
    c1
    cseq
    cfv
    #
    cdiv
    co
    @20
    @27
    @16
    vn
    @29
    @31
    @28
    c1
    @7
    @16
    @7
    cn
    c1
    cuz
    cfv
    wph
    @8
    @11
    simprl
    #
    nnuz
    syl6eleq
    @16
    @9
    cc
    vn
    cv
    #
    @29
    wph
    cA
    cc
    @21
    wf
    #
    @9
    cA
    @10
    wf
    #
    @9
    cc
    @29
    wf
    @15
    wph
    vk
    cA
    cB
    cc
    @21
    fprodmul.2
    @21
    eqid
    #
    fmptd
    #
    @11
    @36
    @8
    @9
    cA
    @10
    f1of
    #
    adantl
    #
    @9
    cA
    cc
    @21
    @10
    fco
    syl2an
    ffvelrnda
    @16
    @9
    cc
    @34
    @31
    wph
    cA
    cc
    @24
    wf
    #
    @36
    @9
    cc
    @31
    wf
    @15
    wph
    vk
    cA
    cC
    cc
    @24
    fprodmul.3
    @24
    eqid
    #
    fmptd
    #
    @40
    @9
    cA
    cc
    @24
    @10
    fco
    syl2an
    ffvelrnda
    @16
    @34
    @9
    wcel
    #
    wa
    #
    @34
    @31
    cfv
    #
    @34
    @10
    cfv
    #
    @24
    cfv
    #
    cc0
    @16
    @36
    @44
    @46
    @48
    wceq
    @16
    @11
    @36
    wph
    @8
    @11
    simprr
    #
    @39
    syl
    #
    @9
    cA
    @34
    @24
    @10
    fvco3
    sylan
    #
    @45
    @47
    cA
    wcel
    #
    vk
    cv
    #
    @24
    cfv
    #
    cc0
    wne
    #
    vk
    cA
    wral
    #
    @48
    cc0
    wne
    #
    @16
    @9
    cA
    @34
    @10
    @50
    ffvelrnda
    #
    wph
    @56
    @15
    @44
    wph
    @55
    vk
    cA
    wph
    @53
    cA
    wcel
    #
    wa
    #
    @54
    cC
    cc0
    @60
    @59
    cC
    cc
    wcel
    @54
    cC
    wceq
    wph
    @59
    simpr
    #
    fprodmul.3
    vk
    cA
    cC
    cc
    @24
    @42
    fvmpt2
    syl2anc
    #
    fproddiv.4
    eqnetrd
    ralrimiva
    ad2antrr
    @55
    @57
    vk
    @47
    cA
    vk
    @48
    cc0
    vk
    cA
    cC
    @47
    nffvmpt1
    #
    vk
    cc0
    nfcv
    nfne
    @53
    @47
    wceq
    #
    @54
    @48
    cc0
    @53
    @47
    @24
    fveq2
    #
    neeq1d
    rspc
    sylc
    eqnetrd
    @45
    @47
    @18
    cfv
    #
    @47
    @21
    cfv
    #
    @48
    cdiv
    co
    #
    @34
    @28
    cfv
    #
    @34
    @29
    cfv
    #
    @46
    cdiv
    co
    @45
    @52
    @53
    @18
    cfv
    #
    @53
    @21
    cfv
    #
    @54
    cdiv
    co
    #
    wceq
    #
    vk
    cA
    wral
    #
    @66
    @68
    wceq
    #
    @58
    wph
    @75
    @15
    @44
    wph
    @74
    vk
    cA
    @60
    @71
    @1
    @73
    @60
    @59
    @1
    cc
    wcel
    @71
    @1
    wceq
    @61
    @60
    cB
    cC
    fprodmul.2
    fprodmul.3
    fproddiv.4
    divcld
    #
    vk
    cA
    @1
    cc
    @18
    @18
    eqid
    #
    fvmpt2
    syl2anc
    @60
    @72
    cB
    @54
    cC
    cdiv
    @60
    @59
    cB
    cc
    wcel
    @72
    cB
    wceq
    @61
    fprodmul.2
    vk
    cA
    cB
    cc
    @21
    @37
    fvmpt2
    syl2anc
    @62
    oveq12d
    eqtr4d
    ralrimiva
    ad2antrr
    @74
    @76
    vk
    @47
    cA
    vk
    @66
    @68
    vk
    cA
    @1
    @47
    nffvmpt1
    vk
    @67
    @48
    cdiv
    vk
    cA
    cB
    @47
    nffvmpt1
    vk
    cdiv
    nfcv
    @63
    nfov
    nfeq
    @64
    @71
    @66
    @73
    @68
    @53
    @47
    @18
    fveq2
    @64
    @72
    @67
    @54
    @48
    cdiv
    @53
    @47
    @21
    fveq2
    @65
    oveq12d
    eqeq12d
    rspc
    sylc
    @16
    @36
    @44
    @69
    @66
    wceq
    @50
    @9
    cA
    @34
    @18
    @10
    fvco3
    sylan
    #
    @45
    @70
    @67
    @46
    @48
    cdiv
    @16
    @36
    @44
    @70
    @67
    wceq
    @50
    @9
    cA
    @34
    @21
    @10
    fvco3
    sylan
    #
    @51
    oveq12d
    3eqtr4d
    prodfdiv
    @16
    cA
    @19
    @66
    vm
    vn
    @10
    @28
    @7
    @17
    @47
    @18
    fveq2
    @33
    @49
    @16
    cA
    cc
    @17
    @18
    wph
    cA
    cc
    @18
    wf
    @15
    wph
    vk
    cA
    @1
    cc
    @18
    @77
    @78
    fmptd
    adantr
    ffvelrnda
    @79
    fprod
    @16
    @23
    @30
    @26
    @32
    cdiv
    @16
    cA
    @22
    @67
    vm
    vn
    @10
    @29
    @7
    @17
    @47
    @21
    fveq2
    @33
    @49
    @16
    cA
    cc
    @17
    @21
    wph
    @35
    @15
    @38
    adantr
    ffvelrnda
    @80
    fprod
    @16
    cA
    @25
    @48
    vm
    vn
    @10
    @31
    @7
    @17
    @47
    @24
    fveq2
    @33
    @49
    @16
    cA
    cc
    @17
    @24
    wph
    @41
    @15
    @43
    adantr
    ffvelrnda
    @51
    fprod
    oveq12d
    3eqtr4d
    cA
    @1
    vm
    vk
    prodfc
    @23
    @3
    @26
    @4
    cdiv
    cA
    cB
    vm
    vk
    prodfc
    cA
    cC
    vm
    vk
    prodfc
    oveq12i
    3eqtr3g
    expr
    exlimdv
    expimpd
    wph
    cA
    cfn
    wcel
    @0
    @13
    wo
    fprodmul.1
    cA
    vf
    fz1f1o
    syl
    mpjaod
end
