include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "prid1.mm"
include "prex.mm"
include "preleq.mm"
include "mpanl12.mm"
include "preq1.mm"
include "eqeq1d.mm"
include "preqr2.mm"
include "syl6bi.mm"
include "imdistani.mm"
include "syl.mm"
include "adantr.mm"
include "preq12.mm"
include "preq2d.mm"
include "eqtrd.mm"
include "impbii.mm"

theorem opthreg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume preleq.1: |- A e. _V
  assume preleq.2: |- B e. _V
  assume preleq.3: |- C e. _V
  assume preleq.4: |- D e. _V


  assert |- ( { A , { A , B } } = { C , { C , D } } <-> ( A = C /\ B = D ) )

  proof
    cA
    cA
    cB
    cpr
    #
    cpr
    #
    cC
    cC
    cD
    cpr
    #
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
    @4
    @5
    @0
    @2
    wceq
    #
    wa
    #
    @7
    cA
    @0
    wcel
    cC
    @2
    wcel
    @4
    @9
    cA
    cB
    preleq.1
    prid1
    cC
    cD
    preleq.3
    prid1
    cA
    @0
    cC
    @2
    preleq.1
    cA
    cB
    prex
    preleq.3
    cC
    cD
    prex
    preleq
    mpanl12
    @5
    @8
    @6
    @5
    @8
    cC
    cB
    cpr
    #
    @2
    wceq
    @6
    @5
    @0
    @10
    @2
    cA
    cC
    cB
    preq1
    eqeq1d
    cB
    cD
    cC
    preleq.2
    preleq.4
    preqr2
    syl6bi
    imdistani
    syl
    @7
    @1
    cC
    @0
    cpr
    #
    @3
    @5
    @1
    @11
    wceq
    @6
    cA
    cC
    @0
    preq1
    adantr
    @7
    @0
    @2
    cC
    cA
    cB
    cC
    cD
    preq12
    preq2d
    eqtrd
    impbii
end
