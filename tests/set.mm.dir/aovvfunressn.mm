include "caov.mm"
include "wcel.mm"
include "cop.mm"
include "cafv.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "df-aov.mm"
include "eleq1i.mm"
include "afvvfunressn.mm"
include "sylbi.mm"

theorem aovvfunressn
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( (( A F B )) e. C -> Fun ( F |` { <. A , B >. } ) )

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
    cF
    @1
    csn
    cres
    wfun
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
    afvvfunressn
    sylbi
end
