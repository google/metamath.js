include "c0.mm"
include "wceq.mm"
include "csu.mm"
include "cfv.mm"
include "chash.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "cc0.mm"
include "caddc.mm"
include "cc.mm"
include "0cn.mm"
include "ffvelrni.mm"
include "ax-mp.mm"
include "addid1i.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "00id.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "vtocl2ga.mm"
include "mp2an.mm"
include "eqtr2i.mm"
include "addcani.mm"
include "mpbi.mm"
include "sumeq1.mm"
include "sum0.mm"
include "3eqtr4a.mm"
include "a1i.mm"
include "cmpt.mm"
include "ccom.mm"
include "cseq.mm"
include "addcl.mm"
include "adantl.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "adantr.mm"
include "simprr.mm"
include "f1of.mm"
include "syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "cuz.mm"
include "simprl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wral.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "cvv.mm"
include "fvex.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nffv.mm"
include "nfeq.mm"
include "rspc.mm"
include "sylc.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "seqhomo.mm"
include "fsum.mm"
include "sumfc.mm"
include "fveq2i.mm"
include "3eqtr3g.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fsumrelem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let vf: setvar f
  let vm: setvar m
  assume fsumre.1: |- ( ph -> A e. Fin )
  assume fsumre.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fsumrelem.3: |- F : CC --> CC
  assume fsumrelem.4: |- ( ( x e. CC /\ y e. CC ) -> ( F ` ( x + y ) ) = ( ( F ` x ) + ( F ` y ) ) )

  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k m
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint B f
  disjoint B m
  disjoint F f
  disjoint F m
  disjoint f ph
  disjoint m ph
  assert |- ( ph -> ( F ` sum_ k e. A B ) = sum_ k e. A ( F ` B ) )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cB
    vk
    csu
    #
    cF
    cfv
    #
    cA
    cB
    cF
    cfv
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
    @0
    @5
    wi
    wph
    @0
    cc0
    cF
    cfv
    #
    cc0
    @2
    @4
    @13
    @13
    caddc
    co
    #
    @13
    cc0
    caddc
    co
    #
    wceq
    @13
    cc0
    wceq
    @15
    @13
    @14
    @13
    cc0
    cc
    wcel
    #
    @13
    cc
    wcel
    0cn
    cc
    cc
    cc0
    cF
    fsumrelem.3
    ffvelrni
    ax-mp
    #
    addid1i
    @16
    @16
    @13
    @14
    wceq
    #
    0cn
    0cn
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    #
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    @20
    cF
    cfv
    #
    caddc
    co
    #
    wceq
    #
    cc0
    @20
    caddc
    co
    #
    cF
    cfv
    #
    @13
    @24
    caddc
    co
    #
    wceq
    @18
    vx
    vy
    cc0
    cc0
    cc
    cc
    @19
    cc0
    wceq
    #
    @22
    @28
    @25
    @29
    @30
    @21
    @27
    cF
    @19
    cc0
    @20
    caddc
    oveq1
    fveq2d
    @30
    @23
    @13
    @24
    caddc
    @19
    cc0
    cF
    fveq2
    oveq1d
    eqeq12d
    @20
    cc0
    wceq
    #
    @28
    @13
    @29
    @14
    @31
    @27
    cc0
    cF
    @31
    @27
    cc0
    cc0
    caddc
    co
    cc0
    @20
    cc0
    cc0
    caddc
    oveq2
    00id
    syl6eq
    fveq2d
    @31
    @24
    @13
    @13
    caddc
    @20
    cc0
    cF
    fveq2
    oveq2d
    eqeq12d
    fsumrelem.4
    vtocl2ga
    mp2an
    eqtr2i
    @13
    @13
    cc0
    @17
    @17
    0cn
    addcani
    mpbi
    @0
    @1
    cc0
    cF
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
    fveq2d
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
    3eqtr4a
    a1i
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
    cF
    cfv
    #
    cA
    @34
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
    @33
    @6
    caddc
    @35
    @9
    ccom
    #
    c1
    cseq
    cfv
    #
    cF
    cfv
    @6
    caddc
    @39
    @9
    ccom
    #
    c1
    cseq
    cfv
    @38
    @41
    @33
    vx
    vy
    caddc
    caddc
    cc
    @42
    @44
    cF
    c1
    @6
    @19
    cc
    wcel
    @20
    cc
    wcel
    wa
    #
    @21
    cc
    wcel
    @33
    @19
    @20
    addcl
    adantl
    @33
    @8
    cc
    @19
    @42
    @33
    cA
    cc
    @35
    wf
    #
    @8
    cA
    @9
    wf
    #
    @8
    cc
    @42
    wf
    wph
    @46
    @32
    wph
    vk
    cA
    cB
    cc
    @35
    fsumre.2
    @35
    eqid
    #
    fmptd
    adantr
    #
    @33
    @10
    @47
    wph
    @7
    @10
    simprr
    #
    @8
    cA
    @9
    f1of
    syl
    #
    @8
    cA
    cc
    @35
    @9
    fco
    syl2anc
    ffvelrnda
    @33
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
    @45
    @26
    @33
    fsumrelem.4
    adantl
    @33
    @19
    @8
    wcel
    #
    wa
    #
    @19
    @9
    cfv
    #
    @35
    cfv
    #
    cF
    cfv
    #
    @55
    @39
    cfv
    #
    @19
    @42
    cfv
    #
    cF
    cfv
    @19
    @44
    cfv
    #
    @54
    @55
    cA
    wcel
    vk
    cv
    #
    @35
    cfv
    #
    cF
    cfv
    #
    @61
    @39
    cfv
    #
    wceq
    #
    vk
    cA
    wral
    #
    @57
    @58
    wceq
    #
    @33
    @8
    cA
    @19
    @9
    @51
    ffvelrnda
    wph
    @66
    @32
    @53
    wph
    @65
    vk
    cA
    wph
    @61
    cA
    wcel
    #
    wa
    #
    @63
    @3
    @64
    @69
    @62
    cB
    cF
    @69
    @68
    cB
    cc
    wcel
    #
    @62
    cB
    wceq
    wph
    @68
    simpr
    #
    fsumre.2
    vk
    cA
    cB
    cc
    @35
    @48
    fvmpt2
    syl2anc
    fveq2d
    @69
    @68
    @3
    cvv
    wcel
    @64
    @3
    wceq
    @71
    cB
    cF
    fvex
    vk
    cA
    @3
    cvv
    @39
    @39
    eqid
    #
    fvmpt2
    sylancl
    eqtr4d
    ralrimiva
    ad2antrr
    @65
    @67
    vk
    @55
    cA
    vk
    @57
    @58
    vk
    @56
    cF
    vk
    cF
    nfcv
    vk
    cA
    cB
    @55
    nffvmpt1
    nffv
    vk
    cA
    @3
    @55
    nffvmpt1
    nfeq
    @61
    @55
    wceq
    #
    @63
    @57
    @64
    @58
    @73
    @62
    @56
    cF
    @61
    @55
    @35
    fveq2
    fveq2d
    @61
    @55
    @39
    fveq2
    eqeq12d
    rspc
    sylc
    @54
    @59
    @56
    cF
    @33
    @47
    @53
    @59
    @56
    wceq
    @51
    @8
    cA
    @19
    @35
    @9
    fvco3
    sylan
    #
    fveq2d
    @33
    @47
    @53
    @60
    @58
    wceq
    @51
    @8
    cA
    @19
    @39
    @9
    fvco3
    sylan
    #
    3eqtr4d
    seqhomo
    @33
    @37
    @43
    cF
    @33
    cA
    @36
    @56
    vm
    vx
    @9
    @42
    @6
    @34
    @55
    @35
    fveq2
    @52
    @50
    @33
    cA
    cc
    @34
    @35
    @49
    ffvelrnda
    @74
    fsum
    fveq2d
    @33
    cA
    @40
    @58
    vm
    vx
    @9
    @44
    @6
    @34
    @55
    @39
    fveq2
    @52
    @50
    @33
    cA
    cc
    @34
    @39
    wph
    cA
    cc
    @39
    wf
    @32
    wph
    vk
    cA
    @3
    cc
    @39
    @69
    @70
    @3
    cc
    wcel
    fsumre.2
    cc
    cc
    cB
    cF
    fsumrelem.3
    ffvelrni
    syl
    @72
    fmptd
    adantr
    ffvelrnda
    @75
    fsum
    3eqtr4d
    @37
    @1
    cF
    cA
    cB
    vm
    vk
    sumfc
    fveq2i
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
    fsumre.1
    cA
    vf
    fz1f1o
    syl
    mpjaod
end
