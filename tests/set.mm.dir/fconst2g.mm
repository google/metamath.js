include "wcel.mm"
include "csn.mm"
include "wf.mm"
include "cxp.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "fvconst.mm"
include "adantlr.mm"
include "fvconst2g.mm"
include "adantll.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fnconstg.mm"
include "eqfnfv.mm"
include "syl2an.mm"
include "mpbird.mm"
include "expcom.mm"
include "fconstg.mm"
include "feq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem fconst2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x


  assert |- ( B e. C -> ( F : A --> { B } <-> F = ( A X. { B } ) ) )

  proof
    cB
    cC
    wcel
    #
    cA
    cB
    csn
    #
    cF
    wf
    #
    cF
    cA
    @1
    cxp
    #
    wceq
    #
    @2
    @0
    @4
    @2
    @0
    wa
    #
    @4
    vx
    cv
    #
    cF
    cfv
    #
    @6
    @3
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @5
    @9
    vx
    cA
    @5
    @6
    cA
    wcel
    #
    wa
    @7
    cB
    @8
    @2
    @11
    @7
    cB
    wceq
    @0
    cA
    cB
    @6
    cF
    fvconst
    adantlr
    @0
    @11
    @8
    cB
    wceq
    @2
    cA
    cB
    @6
    cC
    fvconst2g
    adantll
    eqtr4d
    ralrimiva
    @2
    cF
    cA
    wfn
    @3
    cA
    wfn
    @4
    @10
    wb
    @0
    cA
    @1
    cF
    ffn
    cA
    cB
    cC
    fnconstg
    vx
    cA
    cF
    @3
    eqfnfv
    syl2an
    mpbird
    expcom
    @0
    @2
    @4
    cA
    @1
    @3
    wf
    cA
    cB
    cC
    fconstg
    cA
    @1
    cF
    @3
    feq1
    syl5ibrcom
    impbid
end
