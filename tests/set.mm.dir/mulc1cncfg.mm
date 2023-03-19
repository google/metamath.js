include "cc.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "ccom.mm"
include "cfv.mm"
include "ccncf.mm"
include "wf.mm"
include "wceq.mm"
include "wcel.mm"
include "eqid.mm"
include "mulc1cncf.mm"
include "syl.mm"
include "cncff.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "mulcld.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "oveq2.mm"
include "fvmptf.mm"
include "mpteq2dva.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "cbvmpt.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "cncfco.mm"
include "eqeltrrd.mm"

theorem mulc1cncfg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vt: setvar t
  assume mulc1cncfg.1: |- F/_ x F
  assume mulc1cncfg.2: |- F/ x ph
  assume mulc1cncfg.3: |- ( ph -> F e. ( A -cn-> CC ) )
  assume mulc1cncfg.4: |- ( ph -> B e. CC )

  disjoint A x
  disjoint B x
  disjoint t x
  disjoint A t
  disjoint B t
  disjoint F t
  disjoint ph t
  assert |- ( ph -> ( x e. A |-> ( B x. ( F ` x ) ) ) e. ( A -cn-> CC ) )

  proof
    wph
    vx
    cc
    cB
    vx
    cv
    #
    cmul
    co
    #
    cmpt
    #
    cF
    ccom
    #
    vx
    cA
    cB
    @0
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
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
    @2
    cfv
    #
    cmpt
    #
    @6
    wph
    cc
    cc
    @2
    wf
    #
    cA
    cc
    cF
    wf
    #
    @3
    @11
    wceq
    wph
    @2
    cc
    cc
    ccncf
    co
    wcel
    #
    @12
    wph
    cB
    cc
    wcel
    #
    @14
    mulc1cncfg.4
    vx
    cB
    @2
    @2
    eqid
    #
    mulc1cncf
    syl
    #
    cc
    cc
    @2
    cncff
    syl
    wph
    cF
    @7
    wcel
    @13
    mulc1cncfg.3
    cA
    cc
    cF
    cncff
    syl
    #
    vt
    @2
    cF
    cA
    cc
    cc
    fcompt
    syl2anc
    wph
    @11
    vt
    cA
    cB
    @9
    cmul
    co
    #
    cmpt
    @6
    wph
    vt
    cA
    @10
    @19
    wph
    @8
    cA
    wcel
    #
    wa
    #
    @9
    cc
    wcel
    @19
    cc
    wcel
    @10
    @19
    wceq
    wph
    cA
    cc
    @8
    cF
    @18
    ffvelrnda
    #
    @21
    cB
    @9
    wph
    @15
    @20
    mulc1cncfg.4
    adantr
    @22
    mulcld
    vx
    @9
    @1
    @19
    cc
    @2
    cc
    vx
    @8
    cF
    mulc1cncfg.1
    vx
    @8
    nfcv
    nffv
    #
    vx
    cB
    @9
    cmul
    vx
    cB
    nfcv
    vx
    cmul
    nfcv
    @23
    nfov
    #
    @0
    @9
    cB
    cmul
    oveq2
    @16
    fvmptf
    syl2anc
    mpteq2dva
    vt
    vx
    cA
    @19
    @5
    @24
    vt
    cB
    @4
    cmul
    vt
    cB
    nfcv
    vt
    cmul
    nfcv
    vt
    @4
    nfcv
    nfov
    @8
    @0
    wceq
    @9
    @4
    cB
    cmul
    @8
    @0
    cF
    fveq2
    oveq2d
    cbvmpt
    syl6eq
    eqtrd
    wph
    cA
    cc
    cc
    cF
    @2
    mulc1cncfg.3
    @17
    cncfco
    eqeltrrd
end
