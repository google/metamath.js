include "c0.mm"
include "wceq.mm"
include "cmul.mm"
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
include "1t1e1.mm"
include "prod0.mm"
include "oveq12i.mm"
include "3eqtr4ri.mm"
include "prodeq1.mm"
include "oveq12d.mm"
include "3eqtr4a.mm"
include "a1i.mm"
include "cmpt.mm"
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
include "adantr.mm"
include "f1of.mm"
include "ad2antll.mm"
include "fco.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "wral.mm"
include "simpr.mm"
include "mulcld.mm"
include "fvmpt2.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "sylc.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "prodfmul.mm"
include "simprr.mm"
include "fprod.mm"
include "prodfc.mm"
include "3eqtr3g.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "syl.mm"
include "mpjaod.mm"

theorem fprodmul
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
  assert |- ( ph -> prod_ k e. A ( B x. C ) = ( prod_ k e. A B x. prod_ k e. A C ) )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cB
    cC
    cmul
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
    cmul
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
    c0
    @1
    vk
    cprod
    #
    c0
    cB
    vk
    cprod
    #
    c0
    cC
    vk
    cprod
    #
    cmul
    co
    #
    @2
    @5
    c1
    c1
    cmul
    co
    c1
    @17
    @14
    1t1e1
    @15
    c1
    @16
    c1
    cmul
    cB
    vk
    prod0
    cC
    vk
    prod0
    oveq12i
    @1
    vk
    prod0
    3eqtr4ri
    cA
    c0
    @1
    vk
    prodeq1
    @0
    @3
    @15
    @4
    @16
    cmul
    cA
    c0
    cB
    vk
    prodeq1
    cA
    c0
    cC
    vk
    prodeq1
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
    @20
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
    @20
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
    cmul
    co
    #
    @2
    @5
    @19
    @7
    cmul
    @21
    @10
    ccom
    #
    c1
    cseq
    cfv
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
    @7
    cmul
    @27
    @10
    ccom
    #
    c1
    cseq
    cfv
    #
    cmul
    co
    @23
    @30
    @19
    vn
    @32
    @34
    @31
    c1
    @7
    @19
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
    @19
    @9
    cc
    vn
    cv
    #
    @32
    @19
    cA
    cc
    @24
    wf
    #
    @9
    cA
    @10
    wf
    #
    @9
    cc
    @32
    wf
    wph
    @38
    @18
    wph
    vk
    cA
    cB
    cc
    @24
    fprodmul.2
    @24
    eqid
    #
    fmptd
    adantr
    #
    @11
    @39
    wph
    @8
    @9
    cA
    @10
    f1of
    ad2antll
    #
    @9
    cA
    cc
    @24
    @10
    fco
    syl2anc
    ffvelrnda
    @19
    @9
    cc
    @37
    @34
    @19
    cA
    cc
    @27
    wf
    #
    @39
    @9
    cc
    @34
    wf
    wph
    @43
    @18
    wph
    vk
    cA
    cC
    cc
    @27
    fprodmul.3
    @27
    eqid
    #
    fmptd
    adantr
    #
    @42
    @9
    cA
    cc
    @27
    @10
    fco
    syl2anc
    ffvelrnda
    @19
    @37
    @9
    wcel
    #
    wa
    #
    @37
    @10
    cfv
    #
    @21
    cfv
    #
    @48
    @24
    cfv
    #
    @48
    @27
    cfv
    #
    cmul
    co
    #
    @37
    @31
    cfv
    #
    @37
    @32
    cfv
    #
    @37
    @34
    cfv
    #
    cmul
    co
    @47
    @48
    cA
    wcel
    vk
    cv
    #
    @21
    cfv
    #
    @56
    @24
    cfv
    #
    @56
    @27
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vk
    cA
    wral
    #
    @49
    @52
    wceq
    #
    @19
    @9
    cA
    @37
    @10
    @42
    ffvelrnda
    wph
    @62
    @18
    @46
    wph
    @61
    vk
    cA
    wph
    @56
    cA
    wcel
    #
    wa
    #
    @57
    @1
    @60
    @65
    @64
    @1
    cc
    wcel
    @57
    @1
    wceq
    wph
    @64
    simpr
    #
    @65
    cB
    cC
    fprodmul.2
    fprodmul.3
    mulcld
    #
    vk
    cA
    @1
    cc
    @21
    @21
    eqid
    #
    fvmpt2
    syl2anc
    @65
    @58
    cB
    @59
    cC
    cmul
    @65
    @64
    cB
    cc
    wcel
    @58
    cB
    wceq
    @66
    fprodmul.2
    vk
    cA
    cB
    cc
    @24
    @40
    fvmpt2
    syl2anc
    @65
    @64
    cC
    cc
    wcel
    @59
    cC
    wceq
    @66
    fprodmul.3
    vk
    cA
    cC
    cc
    @27
    @44
    fvmpt2
    syl2anc
    oveq12d
    eqtr4d
    ralrimiva
    ad2antrr
    @61
    @63
    vk
    @48
    cA
    vk
    @49
    @52
    vk
    cA
    @1
    @48
    nffvmpt1
    vk
    @50
    @51
    cmul
    vk
    cA
    cB
    @48
    nffvmpt1
    vk
    cmul
    nfcv
    vk
    cA
    cC
    @48
    nffvmpt1
    nfov
    nfeq
    @56
    @48
    wceq
    #
    @57
    @49
    @60
    @52
    @56
    @48
    @21
    fveq2
    @69
    @58
    @50
    @59
    @51
    cmul
    @56
    @48
    @24
    fveq2
    @56
    @48
    @27
    fveq2
    oveq12d
    eqeq12d
    rspc
    sylc
    @19
    @39
    @46
    @53
    @49
    wceq
    @42
    @9
    cA
    @37
    @21
    @10
    fvco3
    sylan
    #
    @47
    @54
    @50
    @55
    @51
    cmul
    @19
    @39
    @46
    @54
    @50
    wceq
    @42
    @9
    cA
    @37
    @24
    @10
    fvco3
    sylan
    #
    @19
    @39
    @46
    @55
    @51
    wceq
    @42
    @9
    cA
    @37
    @27
    @10
    fvco3
    sylan
    #
    oveq12d
    3eqtr4d
    prodfmul
    @19
    cA
    @22
    @49
    vm
    vn
    @10
    @31
    @7
    @20
    @48
    @21
    fveq2
    @36
    wph
    @8
    @11
    simprr
    #
    @19
    cA
    cc
    @20
    @21
    wph
    cA
    cc
    @21
    wf
    @18
    wph
    vk
    cA
    @1
    cc
    @21
    @67
    @68
    fmptd
    adantr
    ffvelrnda
    @70
    fprod
    @19
    @26
    @33
    @29
    @35
    cmul
    @19
    cA
    @25
    @50
    vm
    vn
    @10
    @32
    @7
    @20
    @48
    @24
    fveq2
    @36
    @73
    @19
    cA
    cc
    @20
    @24
    @41
    ffvelrnda
    @71
    fprod
    @19
    cA
    @28
    @51
    vm
    vn
    @10
    @34
    @7
    @20
    @48
    @27
    fveq2
    @36
    @73
    @19
    cA
    cc
    @20
    @27
    @45
    ffvelrnda
    @72
    fprod
    oveq12d
    3eqtr4d
    cA
    @1
    vm
    vk
    prodfc
    @26
    @3
    @29
    @4
    cmul
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
