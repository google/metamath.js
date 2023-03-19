include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "wo.mm"
include "cpr.mm"
include "wi.mm"
include "prneimg.mm"
include "3adant3.mm"
include "wn.mm"
include "wceq.mm"
include "ioran.mm"
include "ianor.mm"
include "nne.mm"
include "orbi12i.mm"
include "bitri.mm"
include "anbi12i.mm"
include "anddi.mm"
include "eqtr3.mm"
include "eqneqall.mm"
include "syl.mm"
include "preq12.mm"
include "a1d.mm"
include "jaoi.mm"
include "prcom.mm"
include "syl6eq.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "syl5bi.mm"
include "necon1ad.mm"
include "impbid.mm"

theorem prnebg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( ( A e. U /\ B e. V ) /\ ( C e. X /\ D e. Y ) /\ A =/= B ) -> ( ( ( A =/= C /\ A =/= D ) \/ ( B =/= C /\ B =/= D ) ) <-> { A , B } =/= { C , D } ) )

  proof
    cA
    cU
    wcel
    cB
    cV
    wcel
    wa
    #
    cC
    cX
    wcel
    cD
    cY
    wcel
    wa
    #
    cA
    cB
    wne
    #
    w3a
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
    wne
    #
    @0
    @1
    @10
    @13
    wi
    @2
    cA
    cB
    cC
    cD
    cU
    cV
    cX
    cY
    prneimg
    3adant3
    @3
    @10
    @11
    @12
    @10
    wn
    #
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
    @3
    @11
    @12
    wceq
    #
    @14
    @6
    wn
    #
    @9
    wn
    #
    wa
    @21
    @6
    @9
    ioran
    @23
    @17
    @24
    @20
    @23
    @4
    wn
    #
    @5
    wn
    #
    wo
    @17
    @4
    @5
    ianor
    @25
    @15
    @26
    @16
    cA
    cC
    nne
    cA
    cD
    nne
    orbi12i
    bitri
    @24
    @7
    wn
    #
    @8
    wn
    #
    wo
    @20
    @7
    @8
    ianor
    @27
    @18
    @28
    @19
    cB
    cC
    nne
    cB
    cD
    nne
    orbi12i
    bitri
    anbi12i
    bitri
    @21
    @15
    @18
    wa
    #
    @15
    @19
    wa
    #
    wo
    #
    @16
    @18
    wa
    #
    @16
    @19
    wa
    #
    wo
    #
    wo
    #
    @3
    @22
    @15
    @16
    @18
    @19
    anddi
    @2
    @0
    @35
    @22
    wi
    @1
    @35
    @2
    @22
    @31
    @2
    @22
    wi
    #
    @34
    @29
    @36
    @30
    @29
    cA
    cB
    wceq
    #
    @36
    cA
    cB
    cC
    eqtr3
    @22
    cA
    cB
    eqneqall
    #
    syl
    @30
    @22
    @2
    cA
    cB
    cC
    cD
    preq12
    a1d
    jaoi
    @32
    @36
    @33
    @32
    @22
    @2
    @32
    @11
    cD
    cC
    cpr
    @12
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
    @33
    @37
    @36
    cA
    cB
    cD
    eqtr3
    @38
    syl
    jaoi
    jaoi
    com12
    3ad2ant3
    syl5bi
    syl5bi
    necon1ad
    impbid
end
