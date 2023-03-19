include "cop.mm"
include "wdfat.mm"
include "wn.mm"
include "caov.mm"
include "cafv.mm"
include "cvv.mm"
include "df-aov.mm"
include "afvnfundmuv.mm"
include "syl5eq.mm"

theorem aovnfundmuv
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( -. F defAt <. A , B >. -> (( A F B )) = _V )

  proof
    cA
    cB
    cop
    #
    cF
    wdfat
    wn
    cA
    cB
    cF
    caov
    @0
    cF
    cafv
    cvv
    cA
    cB
    cF
    df-aov
    @0
    cF
    afvnfundmuv
    syl5eq
end
