include "cnr.mm"
include "wcel.mm"
include "c0r.mm"
include "wne.mm"
include "cmr.mm"
include "co.mm"
include "cltr.mm"
include "wbr.mm"
include "cv.mm"
include "c1r.mm"
include "wceq.mm"
include "wrex.mm"
include "sqgt0sr.mm"
include "recexsrlem.mm"
include "wa.mm"
include "mulclsr.mm"
include "mulasssr.mm"
include "eqeq1i.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "sylan2b.mm"
include "sylan.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "imp.mm"
include "syldan.mm"

theorem recexsr
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( ( A e. R. /\ A =/= 0R ) -> E. x e. R. ( A .R x ) = 1R )

  proof
    cA
    cnr
    wcel
    #
    cA
    c0r
    wne
    c0r
    cA
    cA
    cmr
    co
    #
    cltr
    wbr
    #
    cA
    vx
    cv
    #
    cmr
    co
    #
    c1r
    wceq
    #
    vx
    cnr
    wrex
    #
    cA
    sqgt0sr
    @0
    @2
    @6
    @2
    @1
    vy
    cv
    #
    cmr
    co
    #
    c1r
    wceq
    #
    vy
    cnr
    wrex
    @0
    @6
    vy
    @1
    recexsrlem
    @0
    @9
    @6
    vy
    cnr
    @0
    @7
    cnr
    wcel
    #
    @9
    @6
    @0
    @10
    wa
    cA
    @7
    cmr
    co
    #
    cnr
    wcel
    #
    @9
    @6
    cA
    @7
    mulclsr
    @9
    @12
    cA
    @11
    cmr
    co
    #
    c1r
    wceq
    #
    @6
    @8
    @13
    c1r
    cA
    cA
    @7
    mulasssr
    eqeq1i
    @5
    @14
    vx
    @11
    cnr
    @3
    @11
    wceq
    @4
    @13
    c1r
    @3
    @11
    cA
    cmr
    oveq2
    eqeq1d
    rspcev
    sylan2b
    sylan
    exp31
    rexlimdv
    syl5
    imp
    syldan
end
