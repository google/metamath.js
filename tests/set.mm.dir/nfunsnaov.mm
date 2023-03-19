include "cop.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wn.mm"
include "caov.mm"
include "cafv.mm"
include "cvv.mm"
include "df-aov.mm"
include "nfunsnafv.mm"
include "syl5eq.mm"

theorem nfunsnaov
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( -. Fun ( F |` { <. A , B >. } ) -> (( A F B )) = _V )

  proof
    cF
    cA
    cB
    cop
    #
    csn
    cres
    wfun
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
    nfunsnafv
    syl5eq
end
