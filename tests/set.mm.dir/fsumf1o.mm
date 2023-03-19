include "c0.mm"
include "wceq.mm"
include "csu.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "cc0.mm"
include "sum0.mm"
include "wfo.mm"
include "f1oeq2.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "f1ofo.mm"
include "fo00.mm"
include "simprbi.mm"
include "3syl.mm"
include "sumeq1d.mm"
include "simpr.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "ex.mm"
include "cmpt.mm"
include "caddc.mm"
include "ccom.mm"
include "cseq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "simprl.mm"
include "simprr.mm"
include "cc.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "fmptd.mm"
include "syldan.mm"
include "adantlr.mm"
include "adantr.mm"
include "f1oco.mm"
include "syl2anc.mm"
include "fvco3.mm"
include "sylan.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "fsum.mm"
include "wral.mm"
include "cid.mm"
include "eqeltrrd.mm"
include "fvmpti.mm"
include "fvmpt2i.mm"
include "adantl.mm"
include "3eqtr4rd.mm"
include "ralrimiva.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "mpan9.mm"
include "sumeq2dv.mm"
include "sumfc.mm"
include "3eqtr3g.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fsumf1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vm: setvar m
  assume fsumf1o.1: |- ( k = G -> B = D )
  assume fsumf1o.2: |- ( ph -> C e. Fin )
  assume fsumf1o.3: |- ( ph -> F : C -1-1-onto-> A )
  assume fsumf1o.4: |- ( ( ph /\ n e. C ) -> ( F ` n ) = G )
  assume fsumf1o.5: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint B n
  disjoint C n
  disjoint D k
  disjoint F n
  disjoint G k
  disjoint k ph
  disjoint n ph
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint A f
  disjoint k m
  disjoint m n
  disjoint A m
  disjoint B f
  disjoint B m
  disjoint C f
  disjoint C m
  disjoint D f
  disjoint D m
  disjoint F f
  disjoint F m
  disjoint f ph
  disjoint m ph
  assert |- ( ph -> sum_ k e. A B = sum_ n e. C D )

  proof
    wph
    cC
    c0
    wceq
    #
    cA
    cB
    vk
    csu
    #
    cC
    cD
    vn
    csu
    #
    wceq
    #
    cC
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @4
    cfz
    co
    #
    cC
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
    @0
    @3
    wph
    @0
    wa
    #
    c0
    cB
    vk
    csu
    cc0
    @1
    @2
    cB
    vk
    sum0
    @11
    cA
    c0
    cB
    vk
    @11
    c0
    cA
    cF
    wf1o
    #
    c0
    cA
    cF
    wfo
    #
    cA
    c0
    wceq
    #
    wph
    @0
    @12
    wph
    cC
    cA
    cF
    wf1o
    #
    @0
    @12
    fsumf1o.3
    cC
    c0
    cA
    cF
    f1oeq2
    syl5ibcom
    imp
    c0
    cA
    cF
    f1ofo
    @13
    cF
    c0
    wceq
    @14
    cA
    cF
    fo00
    simprbi
    3syl
    sumeq1d
    @11
    @2
    c0
    cD
    vn
    csu
    cc0
    @11
    cC
    c0
    cD
    vn
    wph
    @0
    simpr
    sumeq1d
    cD
    vn
    sum0
    syl6eq
    3eqtr4a
    ex
    wph
    @5
    @9
    @3
    wph
    @5
    wa
    @8
    @3
    vf
    wph
    @5
    @8
    @3
    wph
    @5
    @8
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
    cC
    @18
    vn
    cC
    cD
    cmpt
    #
    cfv
    #
    vm
    csu
    #
    @1
    @2
    @17
    cC
    @18
    cF
    cfv
    #
    @19
    cfv
    #
    vm
    csu
    @4
    caddc
    @19
    cF
    @7
    ccom
    #
    ccom
    #
    c1
    cseq
    cfv
    @24
    @21
    @17
    cC
    @26
    vn
    cv
    #
    @7
    cfv
    #
    cF
    cfv
    #
    @19
    cfv
    #
    vm
    vn
    @7
    @28
    @4
    @18
    @30
    wceq
    @25
    @31
    @19
    @18
    @30
    cF
    fveq2
    fveq2d
    wph
    @5
    @8
    simprl
    #
    wph
    @5
    @8
    simprr
    #
    wph
    @18
    cC
    wcel
    #
    @26
    cc
    wcel
    #
    @16
    wph
    @35
    @25
    cA
    wcel
    @36
    wph
    cC
    cA
    @18
    cF
    wph
    @15
    cC
    cA
    cF
    wf
    fsumf1o.3
    cC
    cA
    cF
    f1of
    syl
    #
    ffvelrnda
    wph
    cA
    cc
    @25
    @19
    wph
    vk
    cA
    cB
    cc
    @19
    fsumf1o.5
    @19
    eqid
    #
    fmptd
    #
    ffvelrnda
    syldan
    adantlr
    @17
    @29
    @6
    wcel
    #
    wa
    #
    @29
    @28
    cfv
    #
    @29
    @27
    cfv
    #
    @19
    cfv
    #
    @32
    @17
    @6
    cA
    @27
    wf
    #
    @40
    @42
    @44
    wceq
    @17
    @6
    cA
    @27
    wf1o
    #
    @45
    @17
    @15
    @8
    @46
    wph
    @15
    @16
    fsumf1o.3
    adantr
    @34
    @6
    cC
    cA
    cF
    @7
    f1oco
    syl2anc
    #
    @6
    cA
    @27
    f1of
    syl
    @6
    cA
    @29
    @19
    @27
    fvco3
    sylan
    #
    @41
    @43
    @31
    @19
    @17
    @6
    cC
    @7
    wf
    #
    @40
    @43
    @31
    wceq
    @8
    @49
    wph
    @5
    @6
    cC
    @7
    f1of
    ad2antll
    @6
    cC
    @29
    cF
    @7
    fvco3
    sylan
    fveq2d
    eqtrd
    fsum
    @17
    cC
    @23
    @26
    vm
    wph
    @35
    @23
    @26
    wceq
    #
    @16
    wph
    @29
    @22
    cfv
    #
    @29
    cF
    cfv
    #
    @19
    cfv
    #
    wceq
    #
    vn
    cC
    wral
    @35
    @50
    wph
    @54
    vn
    cC
    wph
    @29
    cC
    wcel
    #
    wa
    #
    cG
    @19
    cfv
    #
    cD
    cid
    cfv
    #
    @53
    @51
    @56
    cG
    cA
    wcel
    @57
    @58
    wceq
    @56
    @52
    cG
    cA
    fsumf1o.4
    wph
    cC
    cA
    @29
    cF
    @37
    ffvelrnda
    eqeltrrd
    vk
    cG
    cB
    cD
    cA
    @19
    fsumf1o.1
    @38
    fvmpti
    syl
    @56
    @52
    cG
    @19
    fsumf1o.4
    fveq2d
    @55
    @51
    @58
    wceq
    wph
    vn
    cC
    cD
    @22
    @22
    eqid
    fvmpt2i
    adantl
    3eqtr4rd
    ralrimiva
    @54
    @50
    vn
    @18
    cC
    vn
    @23
    @26
    vn
    cC
    cD
    @18
    nffvmpt1
    nfeq1
    @29
    @18
    wceq
    #
    @51
    @23
    @53
    @26
    @29
    @18
    @22
    fveq2
    @59
    @52
    @25
    @19
    @29
    @18
    cF
    fveq2
    fveq2d
    eqeq12d
    rspc
    mpan9
    adantlr
    sumeq2dv
    @17
    cA
    @20
    @44
    vm
    vn
    @27
    @28
    @4
    @18
    @43
    @19
    fveq2
    @33
    @47
    @17
    cA
    cc
    @18
    @19
    wph
    cA
    cc
    @19
    wf
    @16
    @39
    adantr
    ffvelrnda
    @48
    fsum
    3eqtr4rd
    cA
    cB
    vm
    vk
    sumfc
    cC
    cD
    vm
    vn
    sumfc
    3eqtr3g
    expr
    exlimdv
    expimpd
    wph
    cC
    cfn
    wcel
    @0
    @10
    wo
    fsumf1o.2
    cC
    vf
    fz1f1o
    syl
    mpjaod
end
