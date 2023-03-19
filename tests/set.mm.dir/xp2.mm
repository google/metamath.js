include "cxp.mm"
include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "elxp7.mm"
include "abbi2i.mm"
include "df-rab.mm"
include "eqtr4i.mm"

theorem xp2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A X. B ) = { x e. ( _V X. _V ) | ( ( 1st ` x ) e. A /\ ( 2nd ` x ) e. B ) }

  proof
    cA
    cB
    cxp
    #
    vx
    cv
    #
    cvv
    cvv
    cxp
    #
    wcel
    @1
    c1st
    cfv
    cA
    wcel
    @1
    c2nd
    cfv
    cB
    wcel
    wa
    #
    wa
    #
    vx
    cab
    @3
    vx
    @2
    crab
    @4
    vx
    @0
    @1
    cA
    cB
    elxp7
    abbi2i
    @3
    vx
    @2
    df-rab
    eqtr4i
end
