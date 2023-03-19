include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "wo.mm"
include "wne.mm"
include "preq12b.mm"
include "idd.mm"
include "wn.mm"
include "wi.mm"
include "df-ne.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "impd.mm"
include "jaod.mm"
include "orc.mm"
include "impbid1.mm"
include "syl5bb.mm"

theorem opthpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume preqr1.a: |- A e. _V
  assume preqr1.b: |- B e. _V
  assume preq12b.c: |- C e. _V
  assume preq12b.d: |- D e. _V


  assert |- ( A =/= D -> ( { A , B } = { C , D } <-> ( A = C /\ B = D ) ) )

  proof
    cA
    cB
    cpr
    cC
    cD
    cpr
    wceq
    cA
    cC
    wceq
    cB
    cD
    wceq
    wa
    #
    cA
    cD
    wceq
    #
    cB
    cC
    wceq
    #
    wa
    #
    wo
    #
    cA
    cD
    wne
    #
    @0
    cA
    cB
    cC
    cD
    preqr1.a
    preqr1.b
    preq12b.c
    preq12b.d
    preq12b
    @5
    @4
    @0
    @5
    @0
    @0
    @3
    @5
    @0
    idd
    @5
    @1
    @2
    @0
    @5
    @1
    wn
    @1
    @2
    @0
    wi
    #
    wi
    cA
    cD
    df-ne
    @1
    @6
    pm2.21
    sylbi
    impd
    jaod
    @0
    @3
    orc
    impbid1
    syl5bb
end
