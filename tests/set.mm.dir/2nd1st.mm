include "cxp.mm"
include "wcel.mm"
include "csn.mm"
include "ccnv.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "1st2nd2.mm"
include "sneqd.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "opswap.mm"
include "syl6eq.mm"

theorem 2nd1st
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B X. C ) -> U. `' { A } = <. ( 2nd ` A ) , ( 1st ` A ) >. )

  proof
    cA
    cB
    cC
    cxp
    wcel
    #
    cA
    csn
    #
    ccnv
    #
    cuni
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
    csn
    #
    ccnv
    #
    cuni
    @4
    @3
    cop
    @0
    @2
    @7
    @0
    @1
    @6
    @0
    cA
    @5
    cA
    cB
    cC
    1st2nd2
    sneqd
    cnveqd
    unieqd
    @3
    @4
    opswap
    syl6eq
end
