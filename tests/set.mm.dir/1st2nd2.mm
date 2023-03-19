include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "elxp6.mm"
include "simplbi.mm"

theorem 1st2nd2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B X. C ) -> A = <. ( 1st ` A ) , ( 2nd ` A ) >. )

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
    @0
    cB
    wcel
    @1
    cC
    wcel
    wa
    cA
    cB
    cC
    elxp6
    simplbi
end
