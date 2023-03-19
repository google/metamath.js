include "clsp.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "wral.mm"
include "cmpt.mm"
include "wss.mm"
include "wf.mm"
include "wcel.mm"
include "wb.mm"
include "eqid.mm"
include "limsuple.mm"
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
include "breq2d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "cbvralv.mm"

theorem limsupge
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  assume limsupge.b: |- ( ph -> B C_ RR )
  assume limsupge.f: |- ( ph -> F : B --> RR* )
  assume limsupge.a: |- ( ph -> A e. RR* )

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
  assert |- ( ph -> ( A <_ ( limsup ` F ) <-> A. k e. RR A <_ sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) ) )

  proof
    wph
    cA
    cF
    clsp
    cfv
    cle
    wbr
    #
    cA
    cF
    vi
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
    cle
    wbr
    #
    vi
    cr
    wral
    #
    cA
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
    cle
    wbr
    #
    vk
    cr
    wral
    #
    wph
    @0
    cA
    @1
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
    cle
    wbr
    #
    vi
    cr
    wral
    #
    @7
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
    @23
    wb
    limsupge.b
    limsupge.f
    limsupge.a
    cA
    cB
    vi
    vj
    cF
    @20
    @20
    eqid
    #
    limsuple
    syl3anc
    wph
    @22
    @6
    vi
    cr
    wph
    @1
    cr
    wcel
    #
    wa
    #
    @21
    @5
    cA
    cle
    @26
    vj
    @1
    @19
    @5
    cr
    @20
    cvv
    @24
    @15
    @1
    wceq
    #
    cxr
    @18
    @4
    clt
    @27
    @17
    @3
    cxr
    @27
    @16
    @2
    cF
    @15
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
    @5
    cvv
    wcel
    @26
    cxr
    @4
    clt
    xrltso
    supex
    a1i
    fvmptd3
    breq2d
    ralbidva
    bitrd
    @7
    @14
    wb
    wph
    @6
    @13
    vi
    vk
    cr
    @1
    @8
    wceq
    #
    @5
    @12
    cA
    cle
    @28
    cxr
    @4
    @11
    clt
    @28
    @3
    @10
    cxr
    @28
    @2
    @9
    cF
    @1
    @8
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    supeq1d
    breq2d
    cbvralv
    a1i
    bitrd
end
