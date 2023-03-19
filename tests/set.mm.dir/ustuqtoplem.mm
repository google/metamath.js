include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "simpl.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "a1i.mm"
include "w3a.mm"
include "simpr2.mm"
include "3anassrs.mm"
include "simpr.mm"
include "mptexg.mm"
include "rnexg.mm"
include "syl.mm"
include "adantr.mm"
include "fvmptd.mm"
include "eleq2d.mm"
include "imaeq1.mm"
include "elrnmpt.mm"
include "sylan9bb.mm"

theorem ustuqtoplem
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cP: class P
  let cU: class U
  let cN: class N
  let cV: class V
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  assume utopustuq.1: |- N = ( p e. X |-> ran ( v e. U |-> ( v " { p } ) ) )

  disjoint A w
  disjoint v w
  disjoint P v
  disjoint P w
  disjoint p v
  disjoint p w
  disjoint U p
  disjoint U v
  disjoint U w
  disjoint X p
  disjoint X v
  disjoint q v
  disjoint q w
  disjoint P q
  disjoint p q
  disjoint U q
  disjoint X q
  assert |- ( ( ( U e. ( UnifOn ` X ) /\ P e. X ) /\ A e. V ) -> ( A e. ( N ` P ) <-> E. w e. U A = ( w " { P } ) ) )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cA
    cP
    cN
    cfv
    #
    wcel
    cA
    vv
    cU
    vv
    cv
    #
    cP
    csn
    #
    cima
    #
    cmpt
    #
    crn
    #
    wcel
    cA
    cV
    wcel
    cA
    vw
    cv
    #
    @6
    cima
    #
    wceq
    vw
    cU
    wrex
    @3
    @4
    @9
    cA
    @3
    vq
    cP
    vv
    cU
    @5
    vq
    cv
    #
    csn
    #
    cima
    #
    cmpt
    #
    crn
    #
    @9
    cX
    cN
    cvv
    cN
    vq
    cX
    @16
    cmpt
    #
    wceq
    @3
    cN
    vp
    cX
    vv
    cU
    @5
    vp
    cv
    #
    csn
    #
    cima
    #
    cmpt
    #
    crn
    #
    cmpt
    @17
    utopustuq.1
    vp
    vq
    cX
    @22
    @16
    @18
    @12
    wceq
    #
    @21
    @15
    @23
    vv
    cU
    @20
    @14
    @23
    @5
    cU
    wcel
    #
    wa
    #
    @19
    @13
    @5
    @25
    @18
    @12
    @23
    @24
    simpl
    sneqd
    imaeq2d
    mpteq2dva
    rneqd
    cbvmptv
    eqtri
    a1i
    @3
    @12
    cP
    wceq
    #
    wa
    #
    @15
    @8
    @27
    vv
    cU
    @14
    @7
    @1
    @2
    @26
    @24
    @14
    @7
    wceq
    @1
    @2
    @26
    @24
    w3a
    wa
    #
    @13
    @6
    @5
    @28
    @12
    cP
    @1
    @2
    @26
    @24
    simpr2
    sneqd
    imaeq2d
    3anassrs
    mpteq2dva
    rneqd
    @1
    @2
    simpr
    @1
    @9
    cvv
    wcel
    #
    @2
    @1
    @8
    cvv
    wcel
    @29
    vv
    cU
    @7
    @0
    mptexg
    @8
    cvv
    rnexg
    syl
    adantr
    fvmptd
    eleq2d
    vw
    cU
    @11
    cA
    @8
    cV
    vv
    vw
    cU
    @7
    @11
    @5
    @10
    @6
    imaeq1
    cbvmptv
    elrnmpt
    sylan9bb
end
