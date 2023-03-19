include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cdp.mm"
include "co.mm"
include "cdp2.mm"
include "dpval.mm"
include "nn0re.mm"
include "dp2cl.mm"
include "sylan.mm"
include "eqeltrd.mm"

theorem dpcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. RR ) -> ( A . B ) e. RR )

  proof
    cA
    cn0
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    cB
    cdp
    co
    cA
    cB
    cdp2
    #
    cr
    cA
    cB
    dpval
    @0
    cA
    cr
    wcel
    @1
    @2
    cr
    wcel
    cA
    nn0re
    cA
    cB
    dp2cl
    sylan
    eqeltrd
end
