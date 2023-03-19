include "wrel.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "crn.mm"
include "1st2nd.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "fvex.mm"
include "opelrn.mm"
include "syl.mm"

theorem 2ndrn
  let cA: class A
  let cR: class R


  assert |- ( ( Rel R /\ A e. R ) -> ( 2nd ` A ) e. ran R )

  proof
    cR
    wrel
    #
    cA
    cR
    wcel
    #
    wa
    #
    cA
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cop
    #
    cR
    wcel
    @4
    cR
    crn
    wcel
    @2
    cA
    @5
    cR
    cA
    cR
    1st2nd
    @0
    @1
    simpr
    eqeltrrd
    @3
    @4
    cR
    cA
    c1st
    fvex
    cA
    c2nd
    fvex
    opelrn
    syl
end
