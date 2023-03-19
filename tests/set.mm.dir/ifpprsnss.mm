include "cpr.mm"
include "wceq.mm"
include "csn.mm"
include "wss.mm"
include "preq2.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "eqcoms.mm"
include "eqeq2d.mm"
include "biimpac.mm"
include "wn.mm"
include "eqimss2.mm"
include "adantr.mm"
include "ifpimpda.mm"

theorem ifpprsnss
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( P = { A , B } -> if- ( A = B , P = { A } , { A , B } C_ P ) )

  proof
    cP
    cA
    cB
    cpr
    #
    wceq
    #
    cA
    cB
    wceq
    #
    cP
    cA
    csn
    #
    wceq
    #
    @0
    cP
    wss
    #
    @2
    @1
    @4
    @2
    @0
    @3
    cP
    @0
    @3
    wceq
    cB
    cA
    cB
    cA
    wceq
    @0
    cA
    cA
    cpr
    @3
    cB
    cA
    cA
    preq2
    cA
    dfsn2
    syl6eqr
    eqcoms
    eqeq2d
    biimpac
    @1
    @5
    @2
    wn
    @0
    cP
    eqimss2
    adantr
    ifpimpda
end
