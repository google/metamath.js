include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "1st2nd2.mm"
include "id.mm"
include "fvex.mm"
include "opelvv.mm"
include "syl6eqel.mm"
include "impbii.mm"

theorem 1st2ndb
  let cA: class A


  assert |- ( A e. ( _V X. _V ) <-> A = <. ( 1st ` A ) , ( 2nd ` A ) >. )

  proof
    cA
    cvv
    cvv
    cxp
    #
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
    #
    wceq
    #
    cA
    cvv
    cvv
    1st2nd2
    @4
    cA
    @3
    @0
    @4
    id
    @1
    @2
    cA
    c1st
    fvex
    cA
    c2nd
    fvex
    opelvv
    syl6eqel
    impbii
end
