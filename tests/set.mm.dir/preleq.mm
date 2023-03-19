include "cpr.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "preq12b.mm"
include "biimpi.mm"
include "ord.mm"
include "en2lp.mm"
include "eleq12.mm"
include "anbi1d.mm"
include "mtbiri.mm"
include "syl6.mm"
include "con4d.mm"
include "impcom.mm"

theorem preleq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume preleq.1: |- A e. _V
  assume preleq.2: |- B e. _V
  assume preleq.3: |- C e. _V
  assume preleq.4: |- D e. _V


  assert |- ( ( ( A e. B /\ C e. D ) /\ { A , B } = { C , D } ) -> ( A = C /\ B = D ) )

  proof
    cA
    cB
    cpr
    cC
    cD
    cpr
    wceq
    #
    cA
    cB
    wcel
    #
    cC
    cD
    wcel
    #
    wa
    #
    cA
    cC
    wceq
    cB
    cD
    wceq
    wa
    #
    @0
    @4
    @3
    @0
    @4
    wn
    cA
    cD
    wceq
    cB
    cC
    wceq
    wa
    #
    @3
    wn
    @0
    @4
    @5
    @0
    @4
    @5
    wo
    cA
    cB
    cC
    cD
    preleq.1
    preleq.2
    preleq.3
    preleq.4
    preq12b
    biimpi
    ord
    @5
    @3
    cD
    cC
    wcel
    #
    @2
    wa
    cD
    cC
    en2lp
    @5
    @1
    @6
    @2
    cA
    cD
    cB
    cC
    eleq12
    anbi1d
    mtbiri
    syl6
    con4d
    impcom
end
