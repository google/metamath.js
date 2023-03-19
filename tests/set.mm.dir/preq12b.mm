include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "wo.mm"
include "wcel.mm"
include "prid1.mm"
include "eleq2.mm"
include "mpbii.mm"
include "elpr.mm"
include "sylib.mm"
include "preq1.mm"
include "eqeq1d.mm"
include "preqr2.mm"
include "syl6bi.mm"
include "com12.mm"
include "ancld.mm"
include "wi.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "sylbi.mm"
include "orim12d.mm"
include "mpd.mm"
include "preq12.mm"
include "syl6eq.mm"
include "jaoi.mm"
include "impbii.mm"

theorem preq12b
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume preqr1.a: |- A e. _V
  assume preqr1.b: |- B e. _V
  assume preq12b.c: |- C e. _V
  assume preq12b.d: |- D e. _V


  assert |- ( { A , B } = { C , D } <-> ( ( A = C /\ B = D ) \/ ( A = D /\ B = C ) ) )

  proof
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
    cC
    wceq
    #
    cB
    cD
    wceq
    #
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
    @2
    @3
    @6
    wo
    #
    @9
    @2
    cA
    @1
    wcel
    #
    @10
    @2
    cA
    @0
    wcel
    @11
    cA
    cB
    preqr1.a
    prid1
    @0
    @1
    cA
    eleq2
    mpbii
    cA
    cC
    cD
    preqr1.a
    elpr
    sylib
    @2
    @3
    @5
    @6
    @8
    @2
    @3
    @4
    @3
    @2
    @4
    @3
    @2
    cC
    cB
    cpr
    #
    @1
    wceq
    @4
    @3
    @0
    @12
    @1
    cA
    cC
    cB
    preq1
    eqeq1d
    cB
    cD
    cC
    preqr1.b
    preq12b.d
    preqr2
    syl6bi
    com12
    ancld
    @2
    @6
    @7
    @2
    @0
    cD
    cC
    cpr
    #
    wceq
    #
    @6
    @7
    wi
    @1
    @13
    @0
    cC
    cD
    prcom
    eqeq2i
    @6
    @14
    @7
    @6
    @14
    cD
    cB
    cpr
    #
    @13
    wceq
    @7
    @6
    @0
    @15
    @13
    cA
    cD
    cB
    preq1
    eqeq1d
    cB
    cC
    cD
    preqr1.b
    preq12b.c
    preqr2
    syl6bi
    com12
    sylbi
    ancld
    orim12d
    mpd
    @5
    @2
    @8
    cA
    cB
    cC
    cD
    preq12
    @8
    @0
    @13
    @1
    cA
    cB
    cD
    cC
    preq12
    cD
    cC
    prcom
    syl6eq
    jaoi
    impbii
end
