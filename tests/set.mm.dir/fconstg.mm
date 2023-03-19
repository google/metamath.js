include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "wceq.mm"
include "wb.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "feq1.mm"
include "feq3.mm"
include "sylan9bb.mm"
include "syl2anc.mm"
include "vex.mm"
include "fconst.mm"
include "vtoclg.mm"

theorem fconstg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( B e. V -> ( A X. { B } ) : A --> { B } )

  proof
    cA
    vx
    cv
    #
    csn
    #
    cA
    @1
    cxp
    #
    wf
    #
    cA
    cB
    csn
    #
    cA
    @4
    cxp
    #
    wf
    #
    vx
    cB
    cV
    @0
    cB
    wceq
    #
    @2
    @5
    wceq
    #
    @1
    @4
    wceq
    #
    @3
    @6
    wb
    @7
    @1
    @4
    cA
    @0
    cB
    sneq
    #
    xpeq2d
    @10
    @8
    @3
    cA
    @1
    @5
    wf
    @9
    @6
    cA
    @1
    @2
    @5
    feq1
    @1
    @4
    cA
    @5
    feq3
    sylan9bb
    syl2anc
    cA
    @0
    vx
    vex
    fconst
    vtoclg
end
