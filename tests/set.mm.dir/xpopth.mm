include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "1st2nd2.mm"
include "eqeqan12d.mm"
include "fvex.mm"
include "opth.mm"
include "syl6rbb.mm"

theorem xpopth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S


  assert |- ( ( A e. ( C X. D ) /\ B e. ( R X. S ) ) -> ( ( ( 1st ` A ) = ( 1st ` B ) /\ ( 2nd ` A ) = ( 2nd ` B ) ) <-> A = B ) )

  proof
    cA
    cC
    cD
    cxp
    wcel
    #
    cB
    cR
    cS
    cxp
    wcel
    #
    wa
    cA
    cB
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
    cB
    c1st
    cfv
    #
    cB
    c2nd
    cfv
    #
    cop
    #
    wceq
    @2
    @5
    wceq
    @3
    @6
    wceq
    wa
    @0
    @1
    cA
    @4
    cB
    @7
    cA
    cC
    cD
    1st2nd2
    cB
    cR
    cS
    1st2nd2
    eqeqan12d
    @2
    @3
    @5
    @6
    cA
    c1st
    fvex
    cA
    c2nd
    fvex
    opth
    syl6rbb
end
