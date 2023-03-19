include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "df-nel.mm"
include "nfel.mm"
include "nfn.mm"
include "nfxfr.mm"

theorem nfnel
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfnel.1: |- F/_ x A
  assume nfnel.2: |- F/_ x B


  assert |- F/ x A e/ B

  proof
    cA
    cB
    wnel
    cA
    cB
    wcel
    #
    wn
    vx
    cA
    cB
    df-nel
    @0
    vx
    vx
    cA
    cB
    nfnel.1
    nfnel.2
    nfel
    nfn
    nfxfr
end
