include "c0.mm"
include "wceq.mm"
include "ccnfld.mm"
include "cmpt.mm"
include "cgsu.mm"
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
include "mpteq1.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cc0.mm"
include "cnfld0.mm"
include "gsum0.mm"
include "sum0.mm"
include "eqtr4i.mm"
include "sumeq1.mm"
include "eqtr4d.mm"
include "a1i.mm"
include "caddc.mm"
include "ccom.mm"
include "cseq.mm"
include "cc.mm"
include "cfn.mm"
include "csupp.mm"
include "ccntz.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "eqid.mm"
include "crg.mm"
include "cmnd.mm"
include "cnring.mm"
include "ringmnd.mm"
include "mp1i.mm"
include "adantr.mm"
include "wf.mm"
include "fmptd.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "cntzcmnf.mm"
include "simprl.mm"
include "wf1.mm"
include "simprr.mm"
include "f1of1.mm"
include "syl.mm"
include "crn.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "sseqtr4d.mm"
include "gsumval3.mm"
include "sumfc.mm"
include "fveq2.mm"
include "ffvelrnda.mm"
include "f1of.mm"
include "fvco3.mm"
include "sylan.mm"
include "fsum.mm"
include "syl5eqr.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem gsumfsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vn: setvar n
  let vx: setvar x
  assume gsumfsum.1: |- ( ph -> A e. Fin )
  assume gsumfsum.2: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint k ph
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B f
  disjoint B n
  disjoint B x
  disjoint f ph
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> ( CCfld gsum ( k e. A |-> B ) ) = sum_ k e. A B )

  proof
    wph
    cA
    c0
    wceq
    #
    ccnfld
    vk
    cA
    cB
    cmpt
    #
    cgsu
    co
    #
    cA
    cB
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
    @5
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
    @4
    wi
    wph
    @0
    @2
    c0
    cB
    vk
    csu
    #
    @3
    @0
    @2
    ccnfld
    c0
    cgsu
    co
    #
    @12
    @0
    @1
    c0
    ccnfld
    cgsu
    @0
    @1
    vk
    c0
    cB
    cmpt
    c0
    vk
    cA
    c0
    cB
    mpteq1
    vk
    cB
    mpt0
    syl6eq
    oveq2d
    @13
    cc0
    @12
    ccnfld
    cc0
    cnfld0
    gsum0
    cB
    vk
    sum0
    eqtr4i
    syl6eq
    cA
    c0
    cB
    vk
    sumeq1
    eqtr4d
    a1i
    wph
    @6
    @10
    @4
    wph
    @6
    wa
    @9
    @4
    vf
    wph
    @6
    @9
    @4
    wph
    @6
    @9
    wa
    #
    wa
    #
    @2
    @5
    caddc
    @1
    @8
    ccom
    #
    c1
    cseq
    cfv
    #
    @3
    @15
    cA
    cc
    caddc
    @1
    ccnfld
    @8
    @5
    cfn
    @16
    cc0
    csupp
    co
    #
    cc0
    ccnfld
    ccntz
    cfv
    #
    cnfldbas
    cnfld0
    cnfldadd
    @19
    eqid
    #
    ccnfld
    crg
    wcel
    #
    ccnfld
    cmnd
    wcel
    @15
    cnring
    ccnfld
    ringmnd
    mp1i
    wph
    cA
    cfn
    wcel
    #
    @14
    gsumfsum.1
    adantr
    wph
    cA
    cc
    @1
    wf
    #
    @14
    wph
    vk
    cA
    cB
    cc
    @1
    gsumfsum.2
    @1
    eqid
    fmptd
    adantr
    #
    @15
    cA
    cc
    @1
    ccnfld
    @19
    cnfldbas
    @20
    @21
    ccnfld
    ccmn
    wcel
    @15
    cnring
    ccnfld
    ringcmn
    mp1i
    @24
    cntzcmnf
    wph
    @6
    @9
    simprl
    #
    @15
    @9
    @7
    cA
    @8
    wf1
    wph
    @6
    @9
    simprr
    #
    @7
    cA
    @8
    f1of1
    syl
    @15
    @1
    cc0
    csupp
    co
    #
    cA
    @8
    crn
    #
    @15
    @1
    cdm
    #
    @27
    cA
    @1
    cc0
    suppssdm
    @15
    @23
    @29
    cA
    wceq
    @24
    cA
    cc
    @1
    fdm
    syl
    syl5sseq
    @15
    @9
    @7
    cA
    @8
    wfo
    @28
    cA
    wceq
    @26
    @7
    cA
    @8
    f1ofo
    @7
    cA
    @8
    forn
    3syl
    sseqtr4d
    @18
    eqid
    gsumval3
    @15
    @3
    cA
    vx
    cv
    #
    @1
    cfv
    #
    vx
    csu
    @17
    cA
    cB
    vx
    vk
    sumfc
    @15
    cA
    @31
    vn
    cv
    #
    @8
    cfv
    #
    @1
    cfv
    #
    vx
    vn
    @8
    @16
    @5
    @30
    @33
    @1
    fveq2
    @25
    @26
    @15
    cA
    cc
    @30
    @1
    @24
    ffvelrnda
    @15
    @7
    cA
    @8
    wf
    #
    @32
    @7
    wcel
    @32
    @16
    cfv
    @34
    wceq
    @15
    @9
    @35
    @26
    @7
    cA
    @8
    f1of
    syl
    @7
    cA
    @32
    @1
    @8
    fvco3
    sylan
    fsum
    syl5eqr
    eqtr4d
    expr
    exlimdv
    expimpd
    wph
    @22
    @0
    @11
    wo
    gsumfsum.1
    cA
    vf
    fz1f1o
    syl
    mpjaod
end
