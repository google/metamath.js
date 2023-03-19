include "cc.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "exp0.mm"
include "mpteq2ia.mm"
include "wtru.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "1cnd.mm"
include "cnmptc.mm"
include "trud.mm"
include "eqeltri.mm"
include "cn0.mm"
include "wa.mm"
include "cmul.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "id.mm"
include "simpl.mm"
include "expp1.mm"
include "syl2anr.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "simpr.mm"
include "syl5eqelr.mm"
include "cnmptid.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "eqeltrd.mm"
include "ex.mm"
include "nn0ind.mm"

theorem expcn
  let vx: setvar x
  let cJ: class J
  let cN: class N
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  assume expcn.j: |- J = ( TopOpen ` CCfld )

  disjoint J x
  disjoint N x
  disjoint A x
  disjoint k n
  disjoint k x
  disjoint J k
  disjoint n x
  disjoint J n
  disjoint N n
  assert |- ( N e. NN0 -> ( x e. CC |-> ( x ^ N ) ) e. ( J Cn J ) )

  proof
    vx
    cc
    vx
    cv
    #
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cJ
    cJ
    ccn
    co
    #
    wcel
    vx
    cc
    @0
    cc0
    cexp
    co
    #
    cmpt
    #
    @4
    wcel
    vx
    cc
    @0
    vk
    cv
    #
    cexp
    co
    #
    cmpt
    #
    @4
    wcel
    #
    vx
    cc
    @0
    @7
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmpt
    #
    @4
    wcel
    #
    vx
    cc
    @0
    cN
    cexp
    co
    #
    cmpt
    #
    @4
    wcel
    vn
    vk
    cN
    @1
    cc0
    wceq
    #
    @3
    @6
    @4
    @17
    vx
    cc
    @2
    @5
    @1
    cc0
    @0
    cexp
    oveq2
    mpteq2dv
    eleq1d
    @1
    @7
    wceq
    #
    @3
    @9
    @4
    @18
    vx
    cc
    @2
    @8
    @1
    @7
    @0
    cexp
    oveq2
    mpteq2dv
    eleq1d
    @1
    @11
    wceq
    #
    @3
    @13
    @4
    @19
    vx
    cc
    @2
    @12
    @1
    @11
    @0
    cexp
    oveq2
    mpteq2dv
    eleq1d
    @1
    cN
    wceq
    #
    @3
    @16
    @4
    @20
    vx
    cc
    @2
    @15
    @1
    cN
    @0
    cexp
    oveq2
    mpteq2dv
    eleq1d
    @6
    vx
    cc
    c1
    cmpt
    #
    @4
    vx
    cc
    @5
    c1
    @0
    exp0
    mpteq2ia
    @21
    @4
    wcel
    wtru
    vx
    c1
    cJ
    cJ
    cc
    cc
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    wtru
    cJ
    expcn.j
    cnfldtopon
    #
    a1i
    #
    @24
    wtru
    1cnd
    cnmptc
    trud
    eqeltri
    @7
    cn0
    wcel
    #
    @10
    @14
    @25
    @10
    wa
    #
    @13
    vn
    cc
    @1
    @7
    cexp
    co
    #
    @1
    cmul
    co
    #
    cmpt
    #
    @4
    @26
    @13
    vn
    cc
    @1
    @11
    cexp
    co
    #
    cmpt
    @29
    vx
    vn
    cc
    @12
    @30
    @0
    @1
    @11
    cexp
    oveq1
    cbvmptv
    @26
    vn
    cc
    @30
    @28
    @1
    cc
    wcel
    #
    @31
    @25
    @30
    @28
    wceq
    @26
    @31
    id
    @25
    @10
    simpl
    @1
    @7
    expp1
    syl2anr
    mpteq2dva
    syl5eq
    @26
    vn
    @27
    @1
    cmul
    cJ
    cJ
    cJ
    cJ
    cc
    @22
    @26
    @23
    a1i
    #
    @26
    vn
    cc
    @27
    cmpt
    @9
    @4
    vx
    vn
    cc
    @8
    @27
    @0
    @1
    @7
    cexp
    oveq1
    cbvmptv
    @25
    @10
    simpr
    syl5eqelr
    @26
    vn
    cJ
    cc
    @32
    cnmptid
    cmul
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    @26
    cJ
    expcn.j
    mulcn
    a1i
    cnmpt12f
    eqeltrd
    ex
    nn0ind
end
