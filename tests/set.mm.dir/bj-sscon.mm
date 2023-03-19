include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cdif.mm"
include "wss.mm"
include "incom.mm"
include "ineq1i.mm"
include "eqeq1i.mm"
include "bj-disj2r.mm"
include "3bitr4i.mm"

theorem bj-sscon
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A i^i V ) C_ ( V \ B ) <-> ( B i^i V ) C_ ( V \ A ) )

  proof
    cA
    cB
    cin
    #
    cV
    cin
    #
    c0
    wceq
    cB
    cA
    cin
    #
    cV
    cin
    #
    c0
    wceq
    cA
    cV
    cin
    cV
    cB
    cdif
    wss
    cB
    cV
    cin
    cV
    cA
    cdif
    wss
    @1
    @3
    c0
    @0
    @2
    cV
    cA
    cB
    incom
    ineq1i
    eqeq1i
    cA
    cB
    cV
    bj-disj2r
    cB
    cA
    cV
    bj-disj2r
    3bitr4i
end
