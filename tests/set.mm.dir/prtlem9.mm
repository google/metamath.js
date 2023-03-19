include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cec.mm"
include "risset.mm"
include "eceq1.mm"
include "reximi.mm"
include "sylbi.mm"

theorem prtlem9
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.sm: class .~

  disjoint A x
  disjoint B x
  assert |- ( A e. B -> E. x e. B [ x ] .~ = [ A ] .~ )

  proof
    cA
    cB
    wcel
    vx
    cv
    #
    cA
    wceq
    #
    vx
    cB
    wrex
    @0
    c.sm
    cec
    cA
    c.sm
    cec
    wceq
    #
    vx
    cB
    wrex
    vx
    cA
    cB
    risset
    @1
    @2
    vx
    cB
    @0
    cA
    c.sm
    eceq1
    reximi
    sylbi
end
