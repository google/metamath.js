include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cdif.mm"
include "cin.mm"
include "wceq.mm"
include "indif2.mm"
include "wss.mm"
include "mblss.mm"
include "df-ss.mm"
include "sylib.mm"
include "difeq1d.mm"
include "syl5eq.mm"
include "adantr.mm"
include "cmmbl.mm"
include "inmbl.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem difmbl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom vol /\ B e. dom vol ) -> ( A \ B ) e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    cA
    cr
    cB
    cdif
    #
    cin
    #
    cA
    cB
    cdif
    #
    @0
    @1
    @4
    @5
    wceq
    @2
    @1
    @4
    cA
    cr
    cin
    #
    cB
    cdif
    @5
    cA
    cr
    cB
    indif2
    @1
    @6
    cA
    cB
    @1
    cA
    cr
    wss
    @6
    cA
    wceq
    cA
    mblss
    cA
    cr
    df-ss
    sylib
    difeq1d
    syl5eq
    adantr
    @2
    @1
    @3
    @0
    wcel
    @4
    @0
    wcel
    cB
    cmmbl
    cA
    @3
    inmbl
    sylan2
    eqeltrrd
end
