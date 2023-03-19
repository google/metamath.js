include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "wn.mm"
include "elxp.mm"
include "0nelop.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "adantr.mm"
include "exlimivv.mm"
include "sylbi.mm"

theorem 0nelelxp
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( C e. ( A X. B ) -> -. (/) e. C )

  proof
    cC
    cA
    cB
    cxp
    wcel
    cC
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @0
    cA
    wcel
    @1
    cB
    wcel
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    c0
    cC
    wcel
    #
    wn
    #
    vx
    vy
    cC
    cA
    cB
    elxp
    @5
    @7
    vx
    vy
    @3
    @7
    @4
    @3
    @6
    c0
    @2
    wcel
    @0
    @1
    0nelop
    cC
    @2
    c0
    eleq2
    mtbiri
    adantr
    exlimivv
    sylbi
end
