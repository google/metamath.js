include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "wo.mm"
include "cpr.mm"
include "wceq.mm"
include "wn.mm"
include "preq12bg.mm"
include "orddi.mm"
include "simpll.mm"
include "pm1.4.mm"
include "ad2antll.mm"
include "jca.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "ianor.mm"
include "nne.mm"
include "orbi12i.mm"
include "bitr2i.mm"
include "anbi12i.mm"
include "syl6ib.mm"
include "pm4.56.mm"
include "necon2ad.mm"

theorem prneimg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( ( A e. U /\ B e. V ) /\ ( C e. X /\ D e. Y ) ) -> ( ( ( A =/= C /\ A =/= D ) \/ ( B =/= C /\ B =/= D ) ) -> { A , B } =/= { C , D } ) )

  proof
    cA
    cU
    wcel
    cB
    cV
    wcel
    wa
    cC
    cX
    wcel
    cD
    cY
    wcel
    wa
    wa
    #
    cA
    cC
    wne
    #
    cA
    cD
    wne
    #
    wa
    #
    cB
    cC
    wne
    #
    cB
    cD
    wne
    #
    wa
    #
    wo
    #
    cA
    cB
    cpr
    #
    cC
    cD
    cpr
    #
    @0
    @8
    @9
    wceq
    #
    @3
    wn
    #
    @6
    wn
    #
    wa
    #
    @7
    wn
    @0
    @10
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
    cB
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wo
    #
    wa
    #
    @13
    @0
    @10
    @14
    @18
    wa
    @15
    @17
    wa
    wo
    #
    @20
    cA
    cB
    cC
    cD
    cU
    cV
    cX
    cY
    preq12bg
    @21
    @16
    @14
    @17
    wo
    #
    wa
    #
    @18
    @15
    wo
    #
    @18
    @17
    wo
    #
    wa
    #
    wa
    #
    @20
    @14
    @18
    @15
    @17
    orddi
    @27
    @16
    @19
    @16
    @22
    @26
    simpll
    @25
    @19
    @23
    @24
    @18
    @17
    pm1.4
    ad2antll
    jca
    sylbi
    syl6bi
    @16
    @11
    @19
    @12
    @11
    @1
    wn
    #
    @2
    wn
    #
    wo
    @16
    @1
    @2
    ianor
    @28
    @14
    @29
    @15
    cA
    cC
    nne
    cA
    cD
    nne
    orbi12i
    bitr2i
    @12
    @4
    wn
    #
    @5
    wn
    #
    wo
    @19
    @4
    @5
    ianor
    @30
    @17
    @31
    @18
    cB
    cC
    nne
    cB
    cD
    nne
    orbi12i
    bitr2i
    anbi12i
    syl6ib
    @3
    @6
    pm4.56
    syl6ib
    necon2ad
end
