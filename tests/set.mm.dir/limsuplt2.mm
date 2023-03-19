include "clsp.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "cr.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "csup.mm"
include "cmpt.mm"
include "wrex.mm"
include "wss.mm"
include "wf.mm"
include "wcel.mm"
include "wb.mm"
include "eqid.mm"
include "limsuplt.mm"
include "syl3anc.mm"
include "wa.mm"
include "cvv.mm"
include "wceq.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "supeq1d.mm"
include "simpr.mm"
include "xrltso.mm"
include "supex.mm"
include "a1i.mm"
include "fvmptd3.mm"
include "breq1d.mm"
include "rexbidva.mm"
include "cbvrexv.mm"
include "3bitrd.mm"

theorem limsuplt2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  assume limsuplt2.1: |- ( ph -> B C_ RR )
  assume limsuplt2.2: |- ( ph -> F : B --> RR* )
  assume limsuplt2.3: |- ( ph -> A e. RR* )

  disjoint A k
  disjoint F k
  disjoint A i
  disjoint i k
  disjoint B i
  disjoint F i
  disjoint F j
  disjoint i j
  disjoint i ph
  disjoint k x
  assert |- ( ph -> ( ( limsup ` F ) < A <-> E. k e. RR sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) < A ) )

  proof
    wph
    cF
    clsp
    cfv
    cA
    clt
    wbr
    #
    vi
    cv
    #
    vj
    cr
    cF
    vj
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    cfv
    #
    cA
    clt
    wbr
    #
    vi
    cr
    wrex
    #
    cF
    @1
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cA
    clt
    wbr
    #
    vi
    cr
    wrex
    #
    cF
    vk
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cA
    clt
    wbr
    #
    vk
    cr
    wrex
    #
    wph
    cB
    cr
    wss
    cB
    cxr
    cF
    wf
    cA
    cxr
    wcel
    @0
    @10
    wb
    limsuplt2.1
    limsuplt2.2
    limsuplt2.3
    cA
    cB
    vi
    vj
    cF
    @7
    @7
    eqid
    #
    limsuplt
    syl3anc
    wph
    @9
    @15
    vi
    cr
    wph
    @1
    cr
    wcel
    #
    wa
    #
    @8
    @14
    cA
    clt
    @26
    vj
    @1
    @6
    @14
    cr
    @7
    cvv
    @24
    @2
    @1
    wceq
    #
    cxr
    @5
    @13
    clt
    @27
    @4
    @12
    cxr
    @27
    @3
    @11
    cF
    @2
    @1
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    supeq1d
    wph
    @25
    simpr
    @14
    cvv
    wcel
    @26
    cxr
    @13
    clt
    xrltso
    supex
    a1i
    fvmptd3
    breq1d
    rexbidva
    @16
    @23
    wb
    wph
    @15
    @22
    vi
    vk
    cr
    @1
    @17
    wceq
    #
    @14
    @21
    cA
    clt
    @28
    cxr
    @13
    @20
    clt
    @28
    @12
    @19
    cxr
    @28
    @11
    @18
    cF
    @1
    @17
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    supeq1d
    breq1d
    cbvrexv
    a1i
    3bitrd
end
