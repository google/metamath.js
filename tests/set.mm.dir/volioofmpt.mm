include "cvol.mm"
include "cioo.mm"
include "ccom.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "nfcv.mm"
include "nfco.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "volioof.mm"
include "a1i.mm"
include "fco.mm"
include "syl2anc.mm"
include "feqmptdf.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "fvvolioof.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem volioofmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume volioofmpt.x: |- F/_ x F
  assume volioofmpt.f: |- ( ph -> F : A --> ( RR* X. RR* ) )

  disjoint A x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( vol o. (,) ) o. F ) = ( x e. A |-> ( vol ` ( ( 1st ` ( F ` x ) ) (,) ( 2nd ` ( F ` x ) ) ) ) ) )

  proof
    wph
    cvol
    cioo
    ccom
    #
    cF
    ccom
    #
    vx
    cA
    vx
    cv
    #
    @1
    cfv
    #
    cmpt
    vx
    cA
    @2
    cF
    cfv
    #
    c1st
    cfv
    @4
    c2nd
    cfv
    cioo
    co
    cvol
    cfv
    #
    cmpt
    wph
    vx
    cA
    cc0
    cpnf
    cicc
    co
    #
    @1
    vx
    cA
    nfcv
    vx
    @0
    cF
    vx
    @0
    nfcv
    volioofmpt.x
    nfco
    wph
    cxr
    cxr
    cxp
    #
    @6
    @0
    wf
    #
    cA
    @7
    cF
    wf
    #
    cA
    @6
    @1
    wf
    @8
    wph
    volioof
    a1i
    volioofmpt.f
    cA
    @7
    @6
    @0
    cF
    fco
    syl2anc
    feqmptdf
    wph
    vx
    cA
    @3
    @5
    wph
    @2
    cA
    wcel
    #
    wa
    cA
    cF
    @2
    wph
    @9
    @10
    volioofmpt.f
    adantr
    wph
    @10
    simpr
    fvvolioof
    mpteq2dva
    eqtrd
end
