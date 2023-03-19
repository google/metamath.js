include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wa.mm"
include "ssid.mm"
include "a1i.mm"
include "preq2.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "eqcoms.mm"
include "adantr.mm"
include "simpr.mm"
include "3sstr4d.mm"
include "1fpid3.mm"

theorem ifpsnprss
  let cA: class A
  let cB: class B
  let cE: class E


  assert |- ( if- ( A = B , E = { A } , { A , B } C_ E ) -> { A , B } C_ E )

  proof
    cA
    cB
    wceq
    #
    cE
    cA
    csn
    #
    wceq
    #
    cA
    cB
    cpr
    #
    cE
    wss
    @0
    @2
    wa
    #
    @1
    @1
    @3
    cE
    @1
    @1
    wss
    @4
    @1
    ssid
    a1i
    @0
    @3
    @1
    wceq
    #
    @2
    @5
    cB
    cA
    cB
    cA
    wceq
    @3
    cA
    cA
    cpr
    @1
    cB
    cA
    cA
    preq2
    cA
    dfsn2
    syl6eqr
    eqcoms
    adantr
    @0
    @2
    simpr
    3sstr4d
    1fpid3
end
