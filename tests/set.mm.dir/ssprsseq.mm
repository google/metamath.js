include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "wb.mm"
include "ssprss.mm"
include "3adant3.mm"
include "wi.mm"
include "eqneqall.mm"
include "eqtr3.mm"
include "syl11.mm"
include "3ad2ant3.mm"
include "com12.mm"
include "preq12.mm"
include "prcom.mm"
include "syl6eq.mm"
include "a1d.mm"
include "ccase.mm"
include "sylbid.mm"
include "eqimss.mm"
include "impbid1.mm"

theorem ssprsseq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W /\ A =/= B ) -> ( { A , B } C_ { C , D } <-> { A , B } = { C , D } ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cB
    cpr
    #
    cC
    cD
    cpr
    #
    wss
    #
    @4
    @5
    wceq
    #
    @3
    @6
    cA
    cC
    wceq
    #
    cA
    cD
    wceq
    #
    wo
    cB
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wo
    wa
    #
    @7
    @0
    @1
    @6
    @12
    wb
    @2
    cA
    cB
    cC
    cD
    cV
    cW
    ssprss
    3adant3
    @12
    @3
    @7
    @8
    @10
    @9
    @11
    @3
    @7
    wi
    @3
    @8
    @10
    wa
    #
    @7
    @2
    @0
    @13
    @7
    wi
    @1
    cA
    cB
    wceq
    #
    @2
    @7
    @13
    @7
    cA
    cB
    eqneqall
    #
    cA
    cB
    cC
    eqtr3
    syl11
    3ad2ant3
    com12
    @9
    @10
    wa
    #
    @7
    @3
    @16
    @4
    cD
    cC
    cpr
    @5
    cA
    cB
    cD
    cC
    preq12
    cD
    cC
    prcom
    syl6eq
    a1d
    @8
    @11
    wa
    @7
    @3
    cA
    cB
    cC
    cD
    preq12
    a1d
    @3
    @9
    @11
    wa
    #
    @7
    @2
    @0
    @17
    @7
    wi
    @1
    @14
    @2
    @7
    @17
    @15
    cA
    cB
    cD
    eqtr3
    syl11
    3ad2ant3
    com12
    ccase
    com12
    sylbid
    @4
    @5
    eqimss
    impbid1
end
