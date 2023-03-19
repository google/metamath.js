include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "cc.mm"
include "ccom.mm"
include "ccncf.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "cbvmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "cn0.mm"
include "adantr.mm"
include "expcld.mm"
include "oveq1.mm"
include "eqid.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "simpr.mm"
include "fmptd.mm"
include "fcompt.mm"
include "eqtr4d.mm"
include "expcncf.mm"
include "cncfco.mm"
include "eqeltrd.mm"

theorem expcnfg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cN: class N
  let vt: setvar t
  assume expcnfg.1: |- F/_ x F
  assume expcnfg.2: |- ( ph -> F e. ( A -cn-> CC ) )
  assume expcnfg.3: |- ( ph -> N e. NN0 )

  disjoint A x
  disjoint N x
  disjoint ph x
  disjoint t x
  disjoint A t
  disjoint F t
  disjoint N t
  disjoint ph t
  assert |- ( ph -> ( x e. A |-> ( ( F ` x ) ^ N ) ) e. ( A -cn-> CC ) )

  proof
    wph
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cN
    cexp
    co
    #
    cmpt
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
    cF
    ccom
    #
    cA
    cc
    ccncf
    co
    #
    wph
    @3
    vt
    cA
    vt
    cv
    #
    cF
    cfv
    #
    @5
    cfv
    #
    cmpt
    #
    @6
    wph
    @3
    vt
    cA
    @9
    cN
    cexp
    co
    #
    cmpt
    @11
    vx
    vt
    cA
    @2
    @12
    vt
    @2
    nfcv
    vx
    @9
    cN
    cexp
    vx
    @8
    cF
    expcnfg.1
    vx
    @8
    nfcv
    nffv
    #
    vx
    cexp
    nfcv
    vx
    cN
    nfcv
    nfov
    #
    @0
    @8
    wceq
    @1
    @9
    cN
    cexp
    @0
    @8
    cF
    fveq2
    oveq1d
    cbvmpt
    wph
    vt
    cA
    @12
    @10
    wph
    @8
    cA
    wcel
    #
    wa
    #
    @10
    @12
    @16
    @9
    cc
    wcel
    @12
    cc
    wcel
    @10
    @12
    wceq
    wph
    cA
    cc
    @8
    cF
    wph
    cF
    @7
    wcel
    cA
    cc
    cF
    wf
    #
    expcnfg.2
    cA
    cc
    cF
    cncff
    syl
    #
    ffvelrnda
    #
    @16
    @9
    cN
    @19
    wph
    cN
    cn0
    wcel
    #
    @15
    expcnfg.3
    adantr
    expcld
    vx
    @9
    @4
    @12
    cc
    @5
    cc
    @13
    @14
    @0
    @9
    cN
    cexp
    oveq1
    @5
    eqid
    #
    fvmptf
    syl2anc
    eqcomd
    mpteq2dva
    syl5eq
    wph
    cc
    cc
    @5
    wf
    @17
    @6
    @11
    wceq
    wph
    vx
    cc
    @4
    cc
    @5
    wph
    @0
    cc
    wcel
    #
    wa
    @0
    cN
    wph
    @22
    simpr
    wph
    @20
    @22
    expcnfg.3
    adantr
    expcld
    @21
    fmptd
    @18
    vt
    @5
    cF
    cA
    cc
    cc
    fcompt
    syl2anc
    eqtr4d
    wph
    cA
    cc
    cc
    cF
    @5
    expcnfg.2
    wph
    @20
    @5
    cc
    cc
    ccncf
    co
    wcel
    expcnfg.3
    vx
    cN
    expcncf
    syl
    cncfco
    eqeltrd
end
