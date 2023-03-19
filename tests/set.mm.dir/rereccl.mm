include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cmul.mm"
include "ax-rrecex.mm"
include "eqcom.mm"
include "cc.mm"
include "wb.mm"
include "1cnd.mm"
include "simpr.mm"
include "recnd.mm"
include "simpll.mm"
include "simplr.mm"
include "divmul.mm"
include "syl112anc.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "risset.mm"
include "sylibr.mm"

theorem rereccl
  let cA: class A
  let vx: setvar x


  assert |- ( ( A e. RR /\ A =/= 0 ) -> ( 1 / A ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    vx
    cv
    #
    c1
    cA
    cdiv
    co
    #
    wceq
    #
    vx
    cr
    wrex
    #
    @4
    cr
    wcel
    @2
    @6
    cA
    @3
    cmul
    co
    c1
    wceq
    #
    vx
    cr
    wrex
    vx
    cA
    ax-rrecex
    @2
    @5
    @7
    vx
    cr
    @5
    @4
    @3
    wceq
    #
    @2
    @3
    cr
    wcel
    #
    wa
    #
    @7
    @3
    @4
    eqcom
    @10
    c1
    cc
    wcel
    @3
    cc
    wcel
    cA
    cc
    wcel
    @1
    @8
    @7
    wb
    @10
    1cnd
    @10
    @3
    @2
    @9
    simpr
    recnd
    @10
    cA
    @0
    @1
    @9
    simpll
    recnd
    @0
    @1
    @9
    simplr
    c1
    @3
    cA
    divmul
    syl112anc
    syl5bb
    rexbidva
    mpbird
    vx
    @4
    cr
    risset
    sylibr
end
