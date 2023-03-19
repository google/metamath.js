include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "wceq.mm"
include "wi.mm"
include "ssdifim.mm"
include "ex.mm"
include "adantr.mm"
include "adantl.mm"
include "impbid.mm"

theorem ssdifsym
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A C_ V /\ B C_ V ) -> ( B = ( V \ A ) <-> A = ( V \ B ) ) )

  proof
    cA
    cV
    wss
    #
    cB
    cV
    wss
    #
    wa
    cB
    cV
    cA
    cdif
    wceq
    #
    cA
    cV
    cB
    cdif
    wceq
    #
    @0
    @2
    @3
    wi
    @1
    @0
    @2
    @3
    cA
    cB
    cV
    ssdifim
    ex
    adantr
    @1
    @3
    @2
    wi
    @0
    @1
    @3
    @2
    cB
    cA
    cV
    ssdifim
    ex
    adantl
    impbid
end
