include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "dfopg.mm"
include "anidms.mm"
include "dfsn2.mm"
include "eqcomi.mm"
include "preq2i.mm"
include "eqtr4i.mm"
include "syl6eq.mm"

theorem opidg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> <. A , A >. = { { A } } )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    cop
    #
    cA
    csn
    #
    cA
    cA
    cpr
    #
    cpr
    #
    @2
    csn
    #
    @0
    @1
    @4
    wceq
    cA
    cA
    cV
    cV
    dfopg
    anidms
    @4
    @2
    @2
    cpr
    @5
    @3
    @2
    @2
    @2
    @3
    cA
    dfsn2
    eqcomi
    preq2i
    @2
    dfsn2
    eqtr4i
    syl6eq
end
