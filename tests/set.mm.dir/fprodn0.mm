include "c0.mm"
include "wceq.mm"
include "cprod.mm"
include "cc0.mm"
include "wne.mm"
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
include "wi.mm"
include "prodeq1.mm"
include "prod0.mm"
include "syl6eq.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "cmul.mm"
include "cmpt.mm"
include "ccom.mm"
include "cseq.mm"
include "prodfc.mm"
include "fveq2.mm"
include "simprl.mm"
include "simprr.mm"
include "cc.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "f1of.mm"
include "syl.mm"
include "fvco3.mm"
include "sylan.mm"
include "fprod.mm"
include "syl5eqr.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fco.mm"
include "syl2anc.mm"
include "adantll.mm"
include "csb.mm"
include "simpr.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "expcom.mm"
include "vtoclgaf.mm"
include "impcom.mm"
include "fvmpts.mm"
include "nfne.mm"
include "neeq1d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "prodfn0.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fprodn0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assume fprodn0.1: |- ( ph -> A e. Fin )
  assume fprodn0.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodn0.3: |- ( ( ph /\ k e. A ) -> B =/= 0 )

  disjoint A k
  disjoint k ph
  disjoint A f
  disjoint A m
  disjoint A n
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f ph
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> prod_ k e. A B =/= 0 )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cB
    vk
    cprod
    #
    cc0
    wne
    #
    cA
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @3
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
    @2
    wi
    wph
    @0
    @1
    c1
    cc0
    @0
    @1
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
    c1
    cc0
    wne
    @0
    ax-1ne0
    a1i
    eqnetrd
    a1i
    wph
    @4
    @8
    @2
    wph
    @4
    wa
    @7
    @2
    vf
    wph
    @4
    @7
    @2
    wph
    @4
    @7
    wa
    #
    wa
    #
    @1
    @3
    cmul
    vk
    cA
    cB
    cmpt
    #
    @6
    ccom
    #
    c1
    cseq
    cfv
    #
    cc0
    @11
    @1
    cA
    vm
    cv
    #
    @12
    cfv
    #
    vm
    cprod
    @14
    cA
    cB
    vm
    vk
    prodfc
    @11
    cA
    @16
    vn
    cv
    #
    @6
    cfv
    #
    @12
    cfv
    #
    vm
    vn
    @6
    @13
    @3
    @15
    @18
    @12
    fveq2
    wph
    @4
    @7
    simprl
    #
    wph
    @4
    @7
    simprr
    #
    @11
    cA
    cc
    @15
    @12
    wph
    cA
    cc
    @12
    wf
    #
    @10
    wph
    vk
    cA
    cB
    cc
    @12
    fprodn0.2
    @12
    eqid
    #
    fmptd
    adantr
    #
    ffvelrnda
    @11
    @5
    cA
    @6
    wf
    #
    @17
    @5
    wcel
    @17
    @13
    cfv
    @19
    wceq
    @11
    @7
    @25
    @21
    @5
    cA
    @6
    f1of
    #
    syl
    #
    @5
    cA
    @17
    @12
    @6
    fvco3
    sylan
    fprod
    syl5eqr
    @11
    vm
    @13
    c1
    @3
    @11
    @3
    cn
    c1
    cuz
    cfv
    @20
    nnuz
    syl6eleq
    @11
    @5
    cc
    @15
    @13
    @11
    @22
    @25
    @5
    cc
    @13
    wf
    @24
    @27
    @5
    cA
    cc
    @12
    @6
    fco
    syl2anc
    ffvelrnda
    @11
    @15
    @5
    wcel
    #
    wa
    @15
    @13
    cfv
    #
    @15
    @6
    cfv
    #
    @12
    cfv
    #
    cc0
    @11
    @25
    @28
    @29
    @31
    wceq
    @27
    @5
    cA
    @15
    @12
    @6
    fvco3
    sylan
    wph
    @10
    @28
    @31
    cc0
    wne
    #
    @10
    @28
    wa
    wph
    @30
    cA
    wcel
    #
    @32
    @7
    @28
    @33
    @4
    @7
    @5
    cA
    @15
    @6
    @26
    ffvelrnda
    adantll
    wph
    @33
    wa
    #
    @31
    vk
    @30
    cB
    csb
    #
    cc0
    @34
    @33
    @35
    cc
    wcel
    #
    @31
    @35
    wceq
    wph
    @33
    simpr
    @33
    wph
    @36
    wph
    cB
    cc
    wcel
    #
    wi
    wph
    @36
    wi
    vk
    @30
    cA
    vk
    @30
    nfcv
    #
    wph
    @36
    vk
    wph
    vk
    nfv
    #
    vk
    @35
    cc
    vk
    @30
    cB
    nfcsb1v
    #
    nfel1
    nfim
    vk
    cv
    #
    @30
    wceq
    #
    @37
    @36
    wph
    @42
    cB
    @35
    cc
    vk
    @30
    cB
    csbeq1a
    #
    eleq1d
    imbi2d
    wph
    @41
    cA
    wcel
    #
    @37
    fprodn0.2
    expcom
    vtoclgaf
    impcom
    vk
    @30
    cB
    cA
    @12
    cc
    @23
    fvmpts
    syl2anc
    @33
    wph
    @35
    cc0
    wne
    #
    wph
    cB
    cc0
    wne
    #
    wi
    wph
    @45
    wi
    vk
    @30
    cA
    @38
    wph
    @45
    vk
    @39
    vk
    @35
    cc0
    @40
    vk
    cc0
    nfcv
    nfne
    nfim
    @42
    @46
    @45
    wph
    @42
    cB
    @35
    cc0
    @43
    neeq1d
    imbi2d
    wph
    @44
    @46
    fprodn0.3
    expcom
    vtoclgaf
    impcom
    eqnetrd
    sylan2
    anassrs
    eqnetrd
    prodfn0
    eqnetrd
    expr
    exlimdv
    expimpd
    wph
    cA
    cfn
    wcel
    @0
    @9
    wo
    fprodn0.1
    cA
    vf
    fz1f1o
    syl
    mpjaod
end
