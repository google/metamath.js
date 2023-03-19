include "c0.mm"
include "wceq.mm"
include "cprod.mm"
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
include "prod0.mm"
include "wfo.mm"
include "adantr.mm"
include "wb.mm"
include "f1oeq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "f1ofo.mm"
include "syl.mm"
include "fo00.mm"
include "simprbi.mm"
include "prodeq1d.mm"
include "prodeq1.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "ex.mm"
include "cmpt.mm"
include "cmul.mm"
include "ccom.mm"
include "cseq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "simprl.mm"
include "simprr.mm"
include "cc.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "fmptd.mm"
include "syldan.mm"
include "adantlr.mm"
include "simpr.mm"
include "f1oco.mm"
include "syl2an.mm"
include "fvco3.mm"
include "sylan.mm"
include "eqtrd.mm"
include "fprod.mm"
include "wral.mm"
include "cid.mm"
include "eqeltrrd.mm"
include "fvmpti.mm"
include "fvmpt2i.mm"
include "3eqtr4rd.mm"
include "ralrimiva.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "weq.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "mpan9.mm"
include "prodeq2dv.mm"
include "prodfc.mm"
include "3eqtr3g.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fprodf1o
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
  assume fprodf1o.1: |- ( k = G -> B = D )
  assume fprodf1o.2: |- ( ph -> C e. Fin )
  assume fprodf1o.3: |- ( ph -> F : C -1-1-onto-> A )
  assume fprodf1o.4: |- ( ( ph /\ n e. C ) -> ( F ` n ) = G )
  assume fprodf1o.5: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint A n
  disjoint B n
  disjoint C n
  disjoint D k
  disjoint F n
  disjoint G k
  disjoint k n
  disjoint k ph
  disjoint n ph
  disjoint A f
  disjoint A m
  disjoint B f
  disjoint B m
  disjoint C f
  disjoint C m
  disjoint D f
  disjoint D m
  disjoint f k
  disjoint f m
  disjoint F m
  disjoint f n
  disjoint f ph
  disjoint k m
  disjoint m n
  disjoint m ph
  assert |- ( ph -> prod_ k e. A B = prod_ n e. C D )

  proof
    wph
    cC
    c0
    wceq
    #
    cA
    cB
    vk
    cprod
    #
    cC
    cD
    vn
    cprod
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
    cprod
    c1
    @1
    @2
    cB
    vk
    prod0
    @11
    cA
    c0
    cB
    vk
    @11
    c0
    cA
    cF
    wfo
    #
    cA
    c0
    wceq
    #
    @11
    c0
    cA
    cF
    wf1o
    #
    @12
    @11
    cC
    cA
    cF
    wf1o
    #
    @14
    wph
    @15
    @0
    fprodf1o.3
    adantr
    @0
    @15
    @14
    wb
    wph
    cC
    c0
    cA
    cF
    f1oeq2
    adantl
    mpbid
    c0
    cA
    cF
    f1ofo
    syl
    @12
    cF
    c0
    wceq
    @13
    cA
    cF
    fo00
    simprbi
    syl
    prodeq1d
    @0
    @2
    c1
    wceq
    wph
    @0
    @2
    c0
    cD
    vn
    cprod
    c1
    cC
    c0
    cD
    vn
    prodeq1
    cD
    vn
    prod0
    syl6eq
    adantl
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
    cprod
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
    cprod
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
    cprod
    @4
    cmul
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
    @34
    @25
    cA
    wcel
    @35
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
    fprodf1o.3
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
    fprodf1o.5
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
    @39
    @41
    @43
    wceq
    @17
    @6
    cA
    @27
    wf1o
    #
    @44
    wph
    @15
    @8
    @45
    @16
    fprodf1o.3
    @5
    @8
    simpr
    @6
    cC
    cA
    cF
    @7
    f1oco
    syl2an
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
    @40
    @42
    @31
    @19
    @17
    @6
    cC
    @7
    wf
    #
    @39
    @42
    @31
    wceq
    @16
    @48
    wph
    @8
    @48
    @5
    @6
    cC
    @7
    f1of
    adantl
    adantl
    @6
    cC
    @29
    cF
    @7
    fvco3
    sylan
    fveq2d
    eqtrd
    fprod
    @17
    cC
    @23
    @26
    vm
    wph
    @34
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
    @34
    @49
    wph
    @53
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
    @52
    @50
    @55
    cG
    cA
    wcel
    @56
    @57
    wceq
    @55
    @51
    cG
    cA
    fprodf1o.4
    wph
    cC
    cA
    @29
    cF
    @36
    ffvelrnda
    eqeltrrd
    vk
    cG
    cB
    cD
    cA
    @19
    fprodf1o.1
    @37
    fvmpti
    syl
    @55
    @51
    cG
    @19
    fprodf1o.4
    fveq2d
    @54
    @50
    @57
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
    @53
    @49
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
    vn
    vm
    weq
    #
    @50
    @23
    @52
    @26
    @29
    @18
    @22
    fveq2
    @58
    @51
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
    prodeq2dv
    @17
    cA
    @20
    @43
    vm
    vn
    @27
    @28
    @4
    @18
    @42
    @19
    fveq2
    @33
    @46
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
    @38
    adantr
    ffvelrnda
    @47
    fprod
    3eqtr4rd
    cA
    cB
    vm
    vk
    prodfc
    cC
    cD
    vm
    vn
    prodfc
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
    fprodf1o.2
    cC
    vf
    fz1f1o
    syl
    mpjaod
end
