include "wcel.mm"
include "cec.mm"
include "wceq.mm"
include "cqs.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "risset.mm"
include "r19.41v.mm"
include "eceq1.mm"
include "eqtr3.mm"
include "eqcomd.mm"
include "sylan.mm"
include "reximi.mm"
include "sylbir.mm"
include "sylanb.mm"
include "elqsg.mm"
include "syl5ibr.mm"
include "expd.mm"

theorem prtlem11
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.sm: class .~
  let vx: setvar x


  assert |- ( B e. D -> ( C e. A -> ( B = [ C ] .~ -> B e. ( A /. .~ ) ) ) )

  proof
    cB
    cD
    wcel
    #
    cC
    cA
    wcel
    #
    cB
    cC
    c.sm
    cec
    #
    wceq
    #
    cB
    cA
    c.sm
    cqs
    wcel
    #
    @1
    @3
    wa
    @4
    @0
    cB
    vx
    cv
    #
    c.sm
    cec
    #
    wceq
    #
    vx
    cA
    wrex
    #
    @1
    @5
    cC
    wceq
    #
    vx
    cA
    wrex
    #
    @3
    @8
    vx
    cC
    cA
    risset
    @10
    @3
    wa
    @9
    @3
    wa
    #
    vx
    cA
    wrex
    @8
    @9
    @3
    vx
    cA
    r19.41v
    @11
    @7
    vx
    cA
    @9
    @6
    @2
    wceq
    #
    @3
    @7
    @5
    cC
    c.sm
    eceq1
    @12
    @3
    wa
    @6
    cB
    @6
    cB
    @2
    eqtr3
    eqcomd
    sylan
    reximi
    sylbir
    sylanb
    vx
    cA
    cB
    c.sm
    cD
    elqsg
    syl5ibr
    expd
end
