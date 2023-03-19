include "cxp.mm"
include "wcel.mm"
include "cvv.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "c2nd.mm"
include "wa.mm"
include "cop.mm"
include "xpss.mm"
include "sseli.mm"
include "elxp6.mm"
include "simplbi.mm"
include "opeq12.mm"
include "sylan9eq.mm"
include "sylan.mm"

theorem eqopi
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. ( V X. W ) /\ ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) ) -> A = <. B , C >. )

  proof
    cA
    cV
    cW
    cxp
    #
    wcel
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    cA
    c1st
    cfv
    #
    cB
    wceq
    cA
    c2nd
    cfv
    #
    cC
    wceq
    wa
    #
    cA
    cB
    cC
    cop
    #
    wceq
    @0
    @1
    cA
    cV
    cW
    xpss
    sseli
    @2
    @5
    cA
    @3
    @4
    cop
    #
    @6
    @2
    cA
    @7
    wceq
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    wa
    cA
    cvv
    cvv
    elxp6
    simplbi
    @3
    @4
    cB
    cC
    opeq12
    sylan9eq
    sylan
end
