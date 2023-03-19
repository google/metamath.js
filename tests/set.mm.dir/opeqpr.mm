include "cop.mm"
include "cpr.mm"
include "wceq.mm"
include "csn.mm"
include "wa.mm"
include "wo.mm"
include "eqcom.mm"
include "dfop.mm"
include "eqeq2i.mm"
include "snex.mm"
include "prex.mm"
include "preq12b.mm"
include "3bitri.mm"

theorem opeqpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opeqpr.1: |- A e. _V
  assume opeqpr.2: |- B e. _V
  assume opeqpr.3: |- C e. _V
  assume opeqpr.4: |- D e. _V


  assert |- ( <. A , B >. = { C , D } <-> ( ( C = { A } /\ D = { A , B } ) \/ ( C = { A , B } /\ D = { A } ) ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cpr
    #
    wceq
    @1
    @0
    wceq
    @1
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    wceq
    cC
    @2
    wceq
    cD
    @3
    wceq
    wa
    cC
    @3
    wceq
    cD
    @2
    wceq
    wa
    wo
    @0
    @1
    eqcom
    @0
    @4
    @1
    cA
    cB
    opeqpr.1
    opeqpr.2
    dfop
    eqeq2i
    cC
    cD
    @2
    @3
    opeqpr.3
    opeqpr.4
    cA
    snex
    cA
    cB
    prex
    preq12b
    3bitri
end
