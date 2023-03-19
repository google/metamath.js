include "wrel.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "wss.mm"
include "df-rel.mm"
include "ssel2.mm"
include "sylanb.mm"
include "1st2nd2.mm"
include "syl.mm"

theorem 1st2nd
  let cA: class A
  let cB: class B


  assert |- ( ( Rel B /\ A e. B ) -> A = <. ( 1st ` A ) , ( 2nd ` A ) >. )

  proof
    cB
    wrel
    #
    cA
    cB
    wcel
    #
    wa
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    cA
    cA
    c1st
    cfv
    cA
    c2nd
    cfv
    cop
    wceq
    @0
    cB
    @2
    wss
    @1
    @3
    cB
    df-rel
    cB
    @2
    cA
    ssel2
    sylanb
    cA
    cvv
    cvv
    1st2nd2
    syl
end
