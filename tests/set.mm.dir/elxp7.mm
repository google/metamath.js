include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "elxp6.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "mpbiran2.mm"
include "anbi1i.mm"
include "bitr4i.mm"

theorem elxp7
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B X. C ) <-> ( A e. ( _V X. _V ) /\ ( ( 1st ` A ) e. B /\ ( 2nd ` A ) e. C ) ) )

  proof
    cA
    cB
    cC
    cxp
    wcel
    cA
    cA
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cop
    wceq
    #
    @0
    cB
    wcel
    @1
    cC
    wcel
    wa
    #
    wa
    cA
    cvv
    cvv
    cxp
    wcel
    #
    @3
    wa
    cA
    cB
    cC
    elxp6
    @4
    @2
    @3
    @4
    @2
    @0
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    wa
    @5
    @6
    cA
    c1st
    fvex
    cA
    c2nd
    fvex
    pm3.2i
    cA
    cvv
    cvv
    elxp6
    mpbiran2
    anbi1i
    bitr4i
end
