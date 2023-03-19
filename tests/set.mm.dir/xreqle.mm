include "cxr.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "xrleid.mm"
include "adantr.mm"
include "simpr.mm"
include "breq2.mm"
include "biimpac.mm"
include "syl2anc.mm"

theorem xreqle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ A = B ) -> A <_ B )

  proof
    cA
    cxr
    wcel
    #
    cA
    cB
    wceq
    #
    wa
    cA
    cA
    cle
    wbr
    #
    @1
    cA
    cB
    cle
    wbr
    #
    @0
    @2
    @1
    cA
    xrleid
    adantr
    @0
    @1
    simpr
    @1
    @2
    @3
    cA
    cB
    cA
    cle
    breq2
    biimpac
    syl2anc
end
