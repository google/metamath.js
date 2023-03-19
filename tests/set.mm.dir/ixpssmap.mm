include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cixp.mm"
include "ciun.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "rgenw.mm"
include "ixpssmapg.mm"
include "ax-mp.mm"

theorem ixpssmap
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ixpssmap.2: |- B e. _V

  disjoint A x
  assert |- X_ x e. A B C_ ( U_ x e. A B ^m A )

  proof
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    vx
    cA
    cB
    cixp
    vx
    cA
    cB
    ciun
    cA
    cmap
    co
    wss
    @0
    vx
    cA
    ixpssmap.2
    rgenw
    vx
    cA
    cB
    cvv
    ixpssmapg
    ax-mp
end
