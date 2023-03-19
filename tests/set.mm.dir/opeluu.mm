include "cop.mm"
include "wcel.mm"
include "cuni.mm"
include "cpr.mm"
include "prid1.mm"
include "opi2.mm"
include "elunii.mm"
include "mpan.mm"
include "sylancr.mm"
include "prid2.mm"
include "jca.mm"

theorem opeluu
  let cA: class A
  let cB: class B
  let cC: class C
  assume opeluu.1: |- A e. _V
  assume opeluu.2: |- B e. _V


  assert |- ( <. A , B >. e. C -> ( A e. U. U. C /\ B e. U. U. C ) )

  proof
    cA
    cB
    cop
    #
    cC
    wcel
    #
    cA
    cC
    cuni
    #
    cuni
    #
    wcel
    #
    cB
    @3
    wcel
    #
    @1
    cA
    cA
    cB
    cpr
    #
    wcel
    @6
    @2
    wcel
    #
    @4
    cA
    cB
    opeluu.1
    prid1
    @6
    @0
    wcel
    @1
    @7
    cA
    cB
    opeluu.1
    opeluu.2
    opi2
    @6
    @0
    cC
    elunii
    mpan
    #
    cA
    @6
    @2
    elunii
    sylancr
    @1
    cB
    @6
    wcel
    @7
    @5
    cA
    cB
    opeluu.2
    prid2
    @8
    cB
    @6
    @2
    elunii
    sylancr
    jca
end
