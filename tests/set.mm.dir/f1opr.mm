include "cxp.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "co.mm"
include "dff13.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "ralxp.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "vex.mm"
include "opth.mm"
include "syl6bb.mm"
include "2ralbii.mm"
include "bitri.mm"
include "anbi2i.mm"

theorem f1opr
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vs: setvar s
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w

  disjoint A r
  disjoint A s
  disjoint A t
  disjoint A u
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint s t
  disjoint s u
  disjoint t u
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint A v
  disjoint A w
  disjoint r v
  disjoint r w
  disjoint s v
  disjoint s w
  disjoint t v
  disjoint t w
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint B v
  disjoint B w
  disjoint F v
  disjoint F w
  assert |- ( F : ( A X. B ) -1-1-> C <-> ( F : ( A X. B ) --> C /\ A. r e. A A. s e. B A. t e. A A. u e. B ( ( r F s ) = ( t F u ) -> ( r = t /\ s = u ) ) ) )

  proof
    cA
    cB
    cxp
    #
    cC
    cF
    wf1
    @0
    cC
    cF
    wf
    #
    vv
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vv
    vw
    weq
    #
    wi
    #
    vw
    @0
    wral
    #
    vv
    @0
    wral
    #
    wa
    @1
    vr
    cv
    #
    vs
    cv
    #
    cF
    co
    #
    vt
    cv
    #
    vu
    cv
    #
    cF
    co
    #
    wceq
    #
    vr
    vt
    weq
    vs
    vu
    weq
    wa
    #
    wi
    #
    vu
    cB
    wral
    vt
    cA
    wral
    #
    vs
    cB
    wral
    vr
    cA
    wral
    #
    wa
    vv
    vw
    @0
    cC
    cF
    dff13
    @10
    @21
    @1
    @10
    @13
    @5
    wceq
    #
    @11
    @12
    cop
    #
    @4
    wceq
    #
    wi
    #
    vw
    @0
    wral
    #
    vs
    cB
    wral
    vr
    cA
    wral
    @21
    @9
    @26
    vv
    vr
    vs
    cA
    cB
    @2
    @23
    wceq
    #
    @8
    @25
    vw
    @0
    @27
    @6
    @22
    @7
    @24
    @27
    @3
    @13
    @5
    @27
    @3
    @23
    cF
    cfv
    @13
    @2
    @23
    cF
    fveq2
    @11
    @12
    cF
    df-ov
    syl6eqr
    eqeq1d
    @2
    @23
    @4
    eqeq1
    imbi12d
    ralbidv
    ralxp
    @26
    @20
    vr
    vs
    cA
    cB
    @25
    @19
    vw
    vt
    vu
    cA
    cB
    @4
    @14
    @15
    cop
    #
    wceq
    #
    @22
    @17
    @24
    @18
    @29
    @5
    @16
    @13
    @29
    @5
    @28
    cF
    cfv
    @16
    @4
    @28
    cF
    fveq2
    @14
    @15
    cF
    df-ov
    syl6eqr
    eqeq2d
    @29
    @24
    @23
    @28
    wceq
    @18
    @4
    @28
    @23
    eqeq2
    @11
    @12
    @14
    @15
    vr
    vex
    vs
    vex
    opth
    syl6bb
    imbi12d
    ralxp
    2ralbii
    bitri
    anbi2i
    bitri
end
