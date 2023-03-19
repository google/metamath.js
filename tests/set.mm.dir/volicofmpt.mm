include "cvol.mm"
include "cico.mm"
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
include "volicoff.mm"
include "feqmptdf.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "cr.mm"
include "wss.mm"
include "ressxr.mm"
include "xpss1.mm"
include "ax-mp.mm"
include "a1i.mm"
include "fssd.mm"
include "adantr.mm"
include "simpr.mm"
include "fvvolicof.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem volicofmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume volicofmpt.1: |- F/_ x F
  assume volicofmpt.2: |- ( ph -> F : A --> ( RR X. RR* ) )

  disjoint A x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( vol o. [,) ) o. F ) = ( x e. A |-> ( vol ` ( ( 1st ` ( F ` x ) ) [,) ( 2nd ` ( F ` x ) ) ) ) ) )

  proof
    wph
    cvol
    cico
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
    cico
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
    volicofmpt.1
    nfco
    wph
    cA
    cF
    volicofmpt.2
    volicoff
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
    cA
    cxr
    cxr
    cxp
    #
    cF
    wf
    @6
    wph
    cA
    cr
    cxr
    cxp
    #
    @7
    cF
    volicofmpt.2
    @8
    @7
    wss
    #
    wph
    cr
    cxr
    wss
    @9
    ressxr
    cr
    cxr
    cxr
    xpss1
    ax-mp
    a1i
    fssd
    adantr
    wph
    @6
    simpr
    fvvolicof
    mpteq2dva
    eqtrd
end
