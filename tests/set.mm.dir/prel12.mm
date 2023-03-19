include "wceq.mm"
include "wn.mm"
include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "prid1.mm"
include "eleq2.mm"
include "mpbii.mm"
include "prid2.mm"
include "jca.mm"
include "wo.mm"
include "wi.mm"
include "elpr.mm"
include "eqeq2.mm"
include "notbid.mm"
include "orel2.mm"
include "syl6bi.mm"
include "impd.mm"
include "com12.mm"
include "ancrd.mm"
include "orel1.mm"
include "orim12d.mm"
include "orcom.mm"
include "bitri.mm"
include "preq12b.mm"
include "3imtr4g.mm"
include "ex.mm"
include "syl5bi.mm"
include "impbid2.mm"

theorem prel12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume preqr1.a: |- A e. _V
  assume preqr1.b: |- B e. _V
  assume preq12b.c: |- C e. _V
  assume preq12b.d: |- D e. _V


  assert |- ( -. A = B -> ( { A , B } = { C , D } <-> ( A e. { C , D } /\ B e. { C , D } ) ) )

  proof
    cA
    cB
    wceq
    #
    wn
    #
    cA
    cB
    cpr
    #
    cC
    cD
    cpr
    #
    wceq
    #
    cA
    @3
    wcel
    #
    cB
    @3
    wcel
    #
    wa
    @4
    @5
    @6
    @4
    cA
    @2
    wcel
    @5
    cA
    cB
    preqr1.a
    prid1
    @2
    @3
    cA
    eleq2
    mpbii
    @4
    cB
    @2
    wcel
    @6
    cA
    cB
    preqr1.b
    prid2
    @2
    @3
    cB
    eleq2
    mpbii
    jca
    @1
    @5
    @6
    @4
    @5
    cA
    cC
    wceq
    #
    cA
    cD
    wceq
    #
    wo
    #
    @1
    @6
    @4
    wi
    #
    cA
    cC
    cD
    preqr1.a
    elpr
    @1
    @9
    @10
    @1
    @9
    wa
    #
    cB
    cD
    wceq
    #
    cB
    cC
    wceq
    #
    wo
    #
    @7
    @12
    wa
    #
    @8
    @13
    wa
    #
    wo
    @6
    @4
    @11
    @12
    @15
    @13
    @16
    @11
    @12
    @7
    @12
    @11
    @7
    @12
    @1
    @9
    @7
    @12
    @1
    @8
    wn
    @9
    @7
    wi
    @12
    @0
    @8
    cB
    cD
    cA
    eqeq2
    notbid
    @8
    @7
    orel2
    syl6bi
    impd
    com12
    ancrd
    @11
    @13
    @8
    @13
    @11
    @8
    @13
    @1
    @9
    @8
    @13
    @1
    @7
    wn
    @9
    @8
    wi
    @13
    @0
    @7
    cB
    cC
    cA
    eqeq2
    notbid
    @7
    @8
    orel1
    syl6bi
    impd
    com12
    ancrd
    orim12d
    @6
    @13
    @12
    wo
    @14
    cB
    cC
    cD
    preqr1.b
    elpr
    @13
    @12
    orcom
    bitri
    cA
    cB
    cC
    cD
    preqr1.a
    preqr1.b
    preq12b.c
    preq12b.d
    preq12b
    3imtr4g
    ex
    syl5bi
    impd
    impbid2
end
