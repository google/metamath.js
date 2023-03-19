include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "leid.mm"
include "breq2.mm"
include "biimpac.mm"
include "sylan.mm"

theorem eqle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ A = B ) -> A <_ B )

  proof
    cA
    cr
    wcel
    cA
    cA
    cle
    wbr
    #
    cA
    cB
    wceq
    #
    cA
    cB
    cle
    wbr
    #
    cA
    leid
    @1
    @0
    @2
    cA
    cB
    cA
    cle
    breq2
    biimpac
    sylan
end
