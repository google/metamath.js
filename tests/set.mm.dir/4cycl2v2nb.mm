include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "prssi.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "syl2anr.mm"
include "anim12i.mm"

theorem 4cycl2v2nb
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( ( ( { A , B } e. E /\ { B , C } e. E ) /\ ( { C , D } e. E /\ { D , A } e. E ) ) -> ( { { A , B } , { B , C } } C_ E /\ { { A , D } , { D , C } } C_ E ) )

  proof
    cA
    cB
    cpr
    #
    cE
    wcel
    cB
    cC
    cpr
    #
    cE
    wcel
    wa
    @0
    @1
    cpr
    cE
    wss
    cC
    cD
    cpr
    #
    cE
    wcel
    #
    cD
    cA
    cpr
    #
    cE
    wcel
    #
    wa
    cA
    cD
    cpr
    #
    cD
    cC
    cpr
    #
    cpr
    cE
    wss
    #
    @0
    @1
    cE
    prssi
    @5
    @6
    cE
    wcel
    #
    @7
    cE
    wcel
    #
    @8
    @3
    @5
    @9
    @4
    @6
    cE
    cD
    cA
    prcom
    eleq1i
    biimpi
    @3
    @10
    @2
    @7
    cE
    cC
    cD
    prcom
    eleq1i
    biimpi
    @6
    @7
    cE
    prssi
    syl2anr
    anim12i
end
