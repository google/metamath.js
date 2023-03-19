include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "cpr.mm"
include "wa.mm"
include "dfop.mm"
include "eqeq1i.mm"
include "snex.mm"
include "prex.mm"
include "preqsn.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "anidm.mm"
include "bitri.mm"
include "3bitri.mm"
include "anbi1i.mm"
include "dfsn2.mm"
include "preq2.mm"
include "syl5req.mm"
include "eqeq1d.mm"
include "syl6bb.mm"
include "pm5.32i.mm"

theorem opeqsn
  let cA: class A
  let cB: class B
  let cC: class C
  assume opeqsn.1: |- A e. _V
  assume opeqsn.2: |- B e. _V
  assume opeqsn.3: |- C e. _V


  assert |- ( <. A , B >. = { C } <-> ( A = B /\ C = { A } ) )

  proof
    cA
    cB
    cop
    #
    cC
    csn
    #
    wceq
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    @1
    wceq
    @2
    @3
    wceq
    #
    @3
    cC
    wceq
    #
    wa
    #
    cA
    cB
    wceq
    #
    cC
    @2
    wceq
    #
    wa
    #
    @0
    @4
    @1
    cA
    cB
    opeqsn.1
    opeqsn.2
    dfop
    eqeq1i
    @2
    @3
    cC
    cA
    snex
    cA
    cB
    prex
    opeqsn.3
    preqsn
    @7
    @8
    @6
    wa
    @10
    @5
    @8
    @6
    @5
    @3
    @2
    wceq
    @8
    cB
    cA
    wceq
    #
    wa
    #
    @8
    @2
    @3
    eqcom
    cA
    cB
    cA
    opeqsn.1
    opeqsn.2
    opeqsn.1
    preqsn
    @12
    @8
    @8
    wa
    @8
    @11
    @8
    @8
    cB
    cA
    eqcom
    anbi2i
    @8
    anidm
    bitri
    3bitri
    anbi1i
    @8
    @6
    @9
    @8
    @6
    @2
    cC
    wceq
    @9
    @8
    @3
    @2
    cC
    @8
    @2
    cA
    cA
    cpr
    @3
    cA
    dfsn2
    cA
    cB
    cA
    preq2
    syl5req
    eqeq1d
    @2
    cC
    eqcom
    syl6bb
    pm5.32i
    bitri
    3bitri
end
