include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "ssdif0.mm"
include "indif1.mm"
include "eqeq1i.mm"
include "bitr4i.mm"
include "biimpri.mm"
include "adantr.mm"
include "inss2.mm"
include "a1i.mm"
include "ssind.mm"
include "adantl.mm"
include "eqssd.mm"

theorem difininv
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( ( A \ C ) i^i B ) = (/) /\ ( ( C \ A ) i^i B ) = (/) ) -> ( A i^i B ) = ( C i^i B ) )

  proof
    cA
    cC
    cdif
    cB
    cin
    #
    c0
    wceq
    #
    cC
    cA
    cdif
    cB
    cin
    #
    c0
    wceq
    #
    wa
    #
    cA
    cB
    cin
    #
    cC
    cB
    cin
    #
    @4
    @5
    cC
    cB
    @1
    @5
    cC
    wss
    #
    @3
    @7
    @1
    @7
    @5
    cC
    cdif
    #
    c0
    wceq
    @1
    @5
    cC
    ssdif0
    @0
    @8
    c0
    cA
    cB
    cC
    indif1
    eqeq1i
    bitr4i
    biimpri
    adantr
    @5
    cB
    wss
    @4
    cA
    cB
    inss2
    a1i
    ssind
    @4
    @6
    cA
    cB
    @3
    @6
    cA
    wss
    #
    @1
    @9
    @3
    @9
    @6
    cA
    cdif
    #
    c0
    wceq
    @3
    @6
    cA
    ssdif0
    @2
    @10
    c0
    cC
    cB
    cA
    indif1
    eqeq1i
    bitr4i
    biimpri
    adantl
    @6
    cB
    wss
    @4
    cC
    cB
    inss2
    a1i
    ssind
    eqssd
end
