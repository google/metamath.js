include "caov.mm"
include "wcel.mm"
include "cop.mm"
include "cafv.mm"
include "cdm.mm"
include "df-aov.mm"
include "eleq1i.mm"
include "afvvdm.mm"
include "sylbi.mm"

theorem aovvdm
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( (( A F B )) e. C -> <. A , B >. e. dom F )

  proof
    cA
    cB
    cF
    caov
    #
    cC
    wcel
    cA
    cB
    cop
    #
    cF
    cafv
    #
    cC
    wcel
    @1
    cF
    cdm
    wcel
    @0
    @2
    cC
    cA
    cB
    cF
    df-aov
    eleq1i
    @1
    cC
    cF
    afvvdm
    sylbi
end
