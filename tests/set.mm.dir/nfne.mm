include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "nfeq.mm"
include "nfn.mm"
include "nfxfr.mm"

theorem nfne
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfne.1: |- F/_ x A
  assume nfne.2: |- F/_ x B


  assert |- F/ x A =/= B

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    #
    wn
    vx
    cA
    cB
    df-ne
    @0
    vx
    vx
    cA
    cB
    nfne.1
    nfne.2
    nfeq
    nfn
    nfxfr
end
