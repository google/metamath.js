include "cpr.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "dfsn2.mm"
include "eqeq2i.mm"
include "wo.mm"
include "preq12b.mm"
include "oridm.mm"
include "eqtr3.mm"
include "simpr.mm"
include "jca.mm"
include "eqtr.mm"
include "impbii.mm"
include "bitri.mm"

theorem preqsnOLD
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
    @3
    cA
    cC
    wceq
    #
    @5
    wa
    #
    @8
    wo
    #
    @6
    cA
    cB
    cC
    cC
    preqsn.1
    preqsn.2
    preqsn.3
    preqsn.3
    preq12b
    @9
    @8
    @6
    @8
    oridm
    @8
    @6
    @8
    @4
    @5
    cA
    cB
    cC
    eqtr3
    @7
    @5
    simpr
    jca
    @6
    @7
    @5
    cA
    cB
    cC
    eqtr
    @4
    @5
    simpr
    jca
    impbii
    bitri
    bitri
    bitri
end
