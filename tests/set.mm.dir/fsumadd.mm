include "c0.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "csu.mm"
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
include "cc0.mm"
include "00id.mm"
include "sum0.mm"
include "oveq12i.mm"
include "3eqtr4ri.mm"
include "sumeq1.mm"
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
include "adantlr.mm"
include "eqid.mm"
include "fmptd.mm"
include "simprr.mm"
include "f1of.mm"
include "syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "wral.mm"
include "cvv.mm"
include "ovex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "adantl.mm"
include "simpr.mm"
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
include "seradd.mm"
include "addcld.mm"
include "fsum.mm"
include "sumfc.mm"
include "3eqtr3g.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fsumadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assume fsumadd.1: |- ( ph -> A e. Fin )
  assume fsumadd.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fsumadd.3: |- ( ( ph /\ k e. A ) -> C e. CC )

  disjoint A k
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
  assert |- ( ph -> sum_ k e. A ( B + C ) = ( sum_ k e. A B + sum_ k e. A C ) )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cB
    cC
    caddc
    co
    #
    vk
    csu
    #
    cA
    cB
    vk
    csu
    #
    cA
    cC
    vk
    csu
    #
    caddc
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
    csu
    #
    c0
    cB
    vk
    csu
    #
    c0
    cC
    vk
    csu
    #
    caddc
    co
    #
    @2
    @5
    cc0
    cc0
    caddc
    co
    cc0
    @17
    @14
    00id
    @15
    cc0
    @16
    cc0
    caddc
    cB
    vk
    sum0
    cC
    vk
    sum0
    oveq12i
    @1
    vk
    sum0
    3eqtr4ri
    cA
    c0
    @1
    vk
    sumeq1
    @0
    @3
    @15
    @4
    @16
    caddc
    cA
    c0
    cB
    vk
    sumeq1
    cA
    c0
    cC
    vk
    sumeq1
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
    csu
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
    csu
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
    csu
    #
    caddc
    co
    #
    @2
    @5
    @19
    @7
    caddc
    @21
    @10
    ccom
    #
    c1
    cseq
    cfv
    @7
    caddc
    @24
    @10
    ccom
    #
    c1
    cseq
    cfv
    #
    @7
    caddc
    @27
    @10
    ccom
    #
    c1
    cseq
    cfv
    #
    caddc
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
    @9
    cA
    @10
    wf
    #
    @9
    cc
    @32
    wf
    @19
    vk
    cA
    cB
    cc
    @24
    wph
    vk
    cv
    #
    cA
    wcel
    #
    cB
    cc
    wcel
    #
    @18
    fsumadd.2
    adantlr
    #
    @24
    eqid
    #
    fmptd
    #
    @19
    @11
    @38
    wph
    @8
    @11
    simprr
    #
    @9
    cA
    @10
    f1of
    syl
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
    @38
    @9
    cc
    @34
    wf
    @19
    vk
    cA
    cC
    cc
    @27
    wph
    @40
    cC
    cc
    wcel
    #
    @18
    fsumadd.3
    adantlr
    #
    @27
    eqid
    #
    fmptd
    #
    @46
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
    @53
    @24
    cfv
    #
    @53
    @27
    cfv
    #
    caddc
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
    caddc
    co
    @52
    @53
    cA
    wcel
    @39
    @21
    cfv
    #
    @39
    @24
    cfv
    #
    @39
    @27
    cfv
    #
    caddc
    co
    #
    wceq
    #
    vk
    cA
    wral
    #
    @54
    @57
    wceq
    #
    @19
    @9
    cA
    @37
    @10
    @46
    ffvelrnda
    wph
    @66
    @18
    @51
    wph
    @65
    vk
    cA
    wph
    @40
    wa
    #
    @61
    @1
    @64
    @40
    @61
    @1
    wceq
    #
    wph
    @40
    @1
    cvv
    wcel
    @69
    cB
    cC
    caddc
    ovex
    vk
    cA
    @1
    cvv
    @21
    @21
    eqid
    #
    fvmpt2
    mpan2
    adantl
    @68
    @62
    cB
    @63
    cC
    caddc
    @68
    @40
    @41
    @62
    cB
    wceq
    wph
    @40
    simpr
    #
    fsumadd.2
    vk
    cA
    cB
    cc
    @24
    @43
    fvmpt2
    syl2anc
    @68
    @40
    @47
    @63
    cC
    wceq
    @71
    fsumadd.3
    vk
    cA
    cC
    cc
    @27
    @49
    fvmpt2
    syl2anc
    oveq12d
    eqtr4d
    ralrimiva
    ad2antrr
    @65
    @67
    vk
    @53
    cA
    vk
    @54
    @57
    vk
    cA
    @1
    @53
    nffvmpt1
    vk
    @55
    @56
    caddc
    vk
    cA
    cB
    @53
    nffvmpt1
    vk
    caddc
    nfcv
    vk
    cA
    cC
    @53
    nffvmpt1
    nfov
    nfeq
    @39
    @53
    wceq
    #
    @61
    @54
    @64
    @57
    @39
    @53
    @21
    fveq2
    @72
    @62
    @55
    @63
    @56
    caddc
    @39
    @53
    @24
    fveq2
    @39
    @53
    @27
    fveq2
    oveq12d
    eqeq12d
    rspc
    sylc
    @19
    @38
    @51
    @58
    @54
    wceq
    @46
    @9
    cA
    @37
    @21
    @10
    fvco3
    sylan
    #
    @52
    @59
    @55
    @60
    @56
    caddc
    @19
    @38
    @51
    @59
    @55
    wceq
    @46
    @9
    cA
    @37
    @24
    @10
    fvco3
    sylan
    #
    @19
    @38
    @51
    @60
    @56
    wceq
    @46
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
    seradd
    @19
    cA
    @22
    @54
    vm
    vn
    @10
    @31
    @7
    @20
    @53
    @21
    fveq2
    @36
    @45
    @19
    cA
    cc
    @20
    @21
    @19
    vk
    cA
    @1
    cc
    @21
    @19
    @40
    wa
    cB
    cC
    @42
    @48
    addcld
    @70
    fmptd
    ffvelrnda
    @73
    fsum
    @19
    @26
    @33
    @29
    @35
    caddc
    @19
    cA
    @25
    @55
    vm
    vn
    @10
    @32
    @7
    @20
    @53
    @24
    fveq2
    @36
    @45
    @19
    cA
    cc
    @20
    @24
    @44
    ffvelrnda
    @74
    fsum
    @19
    cA
    @28
    @56
    vm
    vn
    @10
    @34
    @7
    @20
    @53
    @27
    fveq2
    @36
    @45
    @19
    cA
    cc
    @20
    @27
    @50
    ffvelrnda
    @75
    fsum
    oveq12d
    3eqtr4d
    cA
    @1
    vm
    vk
    sumfc
    @26
    @3
    @29
    @4
    caddc
    cA
    cB
    vm
    vk
    sumfc
    cA
    cC
    vm
    vk
    sumfc
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
    fsumadd.1
    cA
    vf
    fz1f1o
    syl
    mpjaod
end
