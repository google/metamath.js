include "wrel.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wbr.mm"
include "1st2nd.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "df-br.mm"
include "sylibr.mm"

theorem 1st2ndbr
  let cA: class A
  let cB: class B


  assert |- ( ( Rel B /\ A e. B ) -> ( 1st ` A ) B ( 2nd ` A ) )

  proof
    cB
    wrel
    #
    cA
    cB
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
    cB
    wcel
    @3
    @4
    cB
    wbr
    @2
    cA
    @5
    cB
    cA
    cB
    1st2nd
    @0
    @1
    simpr
    eqeltrrd
    @3
    @4
    cB
    df-br
    sylibr
end
