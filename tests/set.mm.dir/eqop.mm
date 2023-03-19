include "cxp.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wa.mm"
include "1st2nd2.mm"
include "eqeq1d.mm"
include "fvex.mm"
include "opth.mm"
include "syl6bb.mm"

theorem eqop
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( A e. ( V X. W ) -> ( A = <. B , C >. <-> ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) ) )

  proof
    cA
    cV
    cW
    cxp
    wcel
    #
    cA
    cB
    cC
    cop
    #
    wceq
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
    @1
    wceq
    @2
    cB
    wceq
    @3
    cC
    wceq
    wa
    @0
    cA
    @4
    @1
    cA
    cV
    cW
    1st2nd2
    eqeq1d
    @2
    @3
    cB
    cC
    cA
    c1st
    fvex
    cA
    c2nd
    fvex
    opth
    syl6bb
end
