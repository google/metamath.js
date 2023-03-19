include "caov.mm"
include "cop.mm"
include "cafv.mm"
include "df-aov.mm"
include "nfop.mm"
include "nfafv.mm"
include "nfcxfr.mm"

theorem nfaov
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  assume nfaov.2: |- F/_ x A
  assume nfaov.3: |- F/_ x F
  assume nfaov.4: |- F/_ x B


  assert |- F/_ x (( A F B ))

  proof
    vx
    cA
    cB
    cF
    caov
    cA
    cB
    cop
    #
    cF
    cafv
    cA
    cB
    cF
    df-aov
    vx
    @0
    cF
    nfaov.3
    vx
    cA
    cB
    nfaov.2
    nfaov.4
    nfop
    nfafv
    nfcxfr
end
