include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "simpl.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "c0ex.mm"
include "fconst.mm"
include "mp1i.mm"
include "eqidd.mm"
include "co.mm"
include "wceq.mm"
include "ffvelrn.mm"
include "subidd.mm"
include "adantll.mm"
include "fvconst2.mm"
include "eqtr4d.mm"
include "offveq.mm"

theorem ofsubid
  let cA: class A
  let cF: class F
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ F : A --> CC ) -> ( F oF - F ) = ( A X. { 0 } ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cc
    cF
    wf
    #
    wa
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    @4
    cmin
    cF
    cF
    cA
    cc0
    csn
    #
    cxp
    #
    cV
    @0
    @1
    simpl
    @1
    cF
    cA
    wfn
    @0
    cA
    cc
    cF
    ffn
    adantl
    #
    @7
    cA
    @5
    @6
    wf
    @6
    cA
    wfn
    @2
    cA
    cc0
    c0ex
    fconst
    cA
    @5
    @6
    ffn
    mp1i
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @4
    eqidd
    #
    @10
    @9
    @4
    @4
    cmin
    co
    #
    cc0
    @3
    @6
    cfv
    #
    @1
    @8
    @11
    cc0
    wceq
    @0
    @1
    @8
    wa
    @4
    cA
    cc
    @3
    cF
    ffvelrn
    subidd
    adantll
    @8
    @12
    cc0
    wceq
    @2
    cA
    cc0
    @3
    c0ex
    fvconst2
    adantl
    eqtr4d
    offveq
end
