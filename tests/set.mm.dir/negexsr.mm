include "cnr.mm"
include "wcel.mm"
include "cm1r.mm"
include "cmr.mm"
include "co.mm"
include "cplr.mm"
include "c0r.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "m1r.mm"
include "mulclsr.mm"
include "mpan2.mm"
include "pn0sr.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem negexsr
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. R. -> E. x e. R. ( A +R x ) = 0R )

  proof
    cA
    cnr
    wcel
    #
    cA
    cm1r
    cmr
    co
    #
    cnr
    wcel
    #
    cA
    @1
    cplr
    co
    #
    c0r
    wceq
    #
    cA
    vx
    cv
    #
    cplr
    co
    #
    c0r
    wceq
    #
    vx
    cnr
    wrex
    @0
    cm1r
    cnr
    wcel
    @2
    m1r
    cA
    cm1r
    mulclsr
    mpan2
    cA
    pn0sr
    @7
    @4
    vx
    @1
    cnr
    @5
    @1
    wceq
    @6
    @3
    c0r
    @5
    @1
    cA
    cplr
    oveq2
    eqeq1d
    rspcev
    syl2anc
end
