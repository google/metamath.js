include "cpr.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "dfsn2.mm"
include "eqeq2i.mm"
include "wo.mm"
include "oridm.mm"
include "preq12b.mm"
include "eqeq2.mm"
include "pm5.32ri.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem preqsn
  let cA: class A
  let cB: class B
  let cC: class C
  assume preqsn.1: |- A e. _V
  assume preqsn.2: |- B e. _V
  assume preqsn.3: |- C e. _V


  assert |- ( { A , B } = { C } <-> ( A = B /\ B = C ) )

  proof
    cA
    cB
    cpr
    #
    cC
    csn
    #
    wceq
    @0
    cC
    cC
    cpr
    #
    wceq
    #
    cA
    cB
    wceq
    #
    cB
    cC
    wceq
    #
    wa
    #
    @1
    @2
    @0
    cC
    dfsn2
    eqeq2i
    cA
    cC
    wceq
    #
    @5
    wa
    #
    @8
    wo
    @8
    @3
    @6
    @8
    oridm
    cA
    cB
    cC
    cC
    preqsn.1
    preqsn.2
    preqsn.3
    preqsn.3
    preq12b
    @5
    @4
    @7
    cB
    cC
    cA
    eqeq2
    pm5.32ri
    3bitr4i
    bitri
end
