include "c0.mm"
include "wceq.mm"
include "csu.mm"
include "cmul.mm"
include "co.mm"
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
include "cc0.mm"
include "mul01d.mm"
include "sumeq1.mm"
include "sum0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "cmpt.mm"
include "caddc.mm"
include "ccom.mm"
include "cseq.mm"
include "cc.mm"
include "addcl.mm"
include "adantl.mm"
include "adantr.mm"
include "adddi.mm"
include "3expb.mm"
include "sylan.mm"
include "cuz.mm"
include "simprl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "f1of.mm"
include "syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "wral.mm"
include "mulcld.mm"
include "fvmpt2.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfeq.mm"
include "fveq2.mm"
include "rspc.mm"
include "sylc.mm"
include "ad2antll.mm"
include "fvco3.mm"
include "3eqtr4d.mm"
include "seqdistr.mm"
include "ffvelrnda.mm"
include "fsum.mm"
include "3eqtr4rd.mm"
include "sumfc.mm"
include "oveq2i.mm"
include "3eqtr3g.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fsummulc2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assume fsummulc2.1: |- ( ph -> A e. Fin )
  assume fsummulc2.2: |- ( ph -> C e. CC )
  assume fsummulc2.3: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint C k
  disjoint k ph
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint f ph
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( C x. sum_ k e. A B ) = sum_ k e. A ( C x. B ) )

  proof
    wph
    cA
    c0
    wceq
    #
    cC
    cA
    cB
    vk
    csu
    #
    cmul
    co
    #
    cA
    cC
    cB
    cmul
    co
    #
    vk
    csu
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
    @6
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
    wph
    @5
    @0
    cC
    cc0
    cmul
    co
    #
    cc0
    wceq
    wph
    cC
    fsummulc2.2
    mul01d
    @0
    @2
    @13
    @4
    cc0
    @0
    @1
    cc0
    cC
    cmul
    @0
    @1
    c0
    cB
    vk
    csu
    cc0
    cA
    c0
    cB
    vk
    sumeq1
    cB
    vk
    sum0
    syl6eq
    oveq2d
    @0
    @4
    c0
    @3
    vk
    csu
    cc0
    cA
    c0
    @3
    vk
    sumeq1
    @3
    vk
    sum0
    syl6eq
    eqeq12d
    syl5ibrcom
    wph
    @7
    @11
    @5
    wph
    @7
    wa
    @10
    @5
    vf
    wph
    @7
    @10
    @5
    wph
    @7
    @10
    wa
    #
    wa
    #
    cC
    cA
    vm
    cv
    #
    vk
    cA
    cB
    cmpt
    #
    cfv
    #
    vm
    csu
    #
    cmul
    co
    #
    cA
    @16
    vk
    cA
    @3
    cmpt
    #
    cfv
    #
    vm
    csu
    #
    @2
    @4
    @15
    @6
    caddc
    @21
    @9
    ccom
    #
    c1
    cseq
    cfv
    cC
    @6
    caddc
    @17
    @9
    ccom
    #
    c1
    cseq
    cfv
    #
    cmul
    co
    @23
    @20
    @15
    vn
    vm
    cC
    caddc
    cc
    cmul
    @24
    @25
    c1
    @6
    vn
    cv
    #
    cc
    wcel
    #
    @16
    cc
    wcel
    #
    wa
    #
    @27
    @16
    caddc
    co
    #
    cc
    wcel
    @15
    @27
    @16
    addcl
    adantl
    @15
    cC
    cc
    wcel
    #
    @30
    cC
    @31
    cmul
    co
    cC
    @27
    cmul
    co
    cC
    @16
    cmul
    co
    caddc
    co
    wceq
    #
    wph
    @32
    @14
    fsummulc2.2
    adantr
    @32
    @28
    @29
    @33
    cC
    @27
    @16
    adddi
    3expb
    sylan
    @15
    @6
    cn
    c1
    cuz
    cfv
    wph
    @7
    @10
    simprl
    #
    nnuz
    syl6eleq
    @15
    @27
    @8
    wcel
    #
    wa
    #
    @8
    cc
    @27
    @25
    @36
    cA
    cc
    @17
    wf
    #
    @8
    cA
    @9
    wf
    #
    @8
    cc
    @25
    wf
    wph
    @37
    @14
    @35
    wph
    vk
    cA
    cB
    cc
    @17
    fsummulc2.3
    @17
    eqid
    #
    fmptd
    #
    ad2antrr
    @36
    @10
    @38
    @15
    @10
    @35
    wph
    @7
    @10
    simprr
    #
    adantr
    @8
    cA
    @9
    f1of
    #
    syl
    #
    @8
    cA
    cc
    @17
    @9
    fco
    syl2anc
    @15
    @35
    simpr
    #
    ffvelrnd
    @36
    @27
    @9
    cfv
    #
    @21
    cfv
    #
    cC
    @45
    @17
    cfv
    #
    cmul
    co
    #
    @27
    @24
    cfv
    #
    cC
    @27
    @25
    cfv
    #
    cmul
    co
    @36
    @45
    cA
    wcel
    vk
    cv
    #
    @21
    cfv
    #
    cC
    @51
    @17
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
    @46
    @48
    wceq
    #
    @36
    @8
    cA
    @27
    @9
    @43
    @44
    ffvelrnd
    wph
    @56
    @14
    @35
    wph
    @55
    vk
    cA
    wph
    @51
    cA
    wcel
    #
    wa
    #
    @52
    @3
    @54
    @59
    @58
    @3
    cc
    wcel
    @52
    @3
    wceq
    wph
    @58
    simpr
    #
    @59
    cC
    cB
    wph
    @32
    @58
    fsummulc2.2
    adantr
    fsummulc2.3
    mulcld
    #
    vk
    cA
    @3
    cc
    @21
    @21
    eqid
    #
    fvmpt2
    syl2anc
    @59
    @53
    cB
    cC
    cmul
    @59
    @58
    cB
    cc
    wcel
    @53
    cB
    wceq
    @60
    fsummulc2.3
    vk
    cA
    cB
    cc
    @17
    @39
    fvmpt2
    syl2anc
    oveq2d
    eqtr4d
    ralrimiva
    ad2antrr
    @55
    @57
    vk
    @45
    cA
    vk
    @46
    @48
    vk
    cA
    @3
    @45
    nffvmpt1
    vk
    cC
    @47
    cmul
    vk
    cC
    nfcv
    vk
    cmul
    nfcv
    vk
    cA
    cB
    @45
    nffvmpt1
    nfov
    nfeq
    @51
    @45
    wceq
    #
    @52
    @46
    @54
    @48
    @51
    @45
    @21
    fveq2
    @63
    @53
    @47
    cC
    cmul
    @51
    @45
    @17
    fveq2
    oveq2d
    eqeq12d
    rspc
    sylc
    @15
    @38
    @35
    @49
    @46
    wceq
    @10
    @38
    wph
    @7
    @42
    ad2antll
    #
    @8
    cA
    @27
    @21
    @9
    fvco3
    sylan
    #
    @36
    @50
    @47
    cC
    cmul
    @15
    @38
    @35
    @50
    @47
    wceq
    @64
    @8
    cA
    @27
    @17
    @9
    fvco3
    sylan
    #
    oveq2d
    3eqtr4d
    seqdistr
    @15
    cA
    @22
    @46
    vm
    vn
    @9
    @24
    @6
    @16
    @45
    @21
    fveq2
    @34
    @41
    @15
    cA
    cc
    @16
    @21
    wph
    cA
    cc
    @21
    wf
    @14
    wph
    vk
    cA
    @3
    cc
    @21
    @61
    @62
    fmptd
    adantr
    ffvelrnda
    @65
    fsum
    @15
    @19
    @26
    cC
    cmul
    @15
    cA
    @18
    @47
    vm
    vn
    @9
    @25
    @6
    @16
    @45
    @17
    fveq2
    @34
    @41
    @15
    cA
    cc
    @16
    @17
    wph
    @37
    @14
    @40
    adantr
    ffvelrnda
    @66
    fsum
    oveq2d
    3eqtr4rd
    @19
    @1
    cC
    cmul
    cA
    cB
    vm
    vk
    sumfc
    oveq2i
    cA
    @3
    vm
    vk
    sumfc
    3eqtr3g
    expr
    exlimdv
    expimpd
    wph
    cA
    cfn
    wcel
    @0
    @12
    wo
    fsummulc2.1
    cA
    vf
    fz1f1o
    syl
    mpjaod
end
