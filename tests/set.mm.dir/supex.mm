include "wor.mm"
include "csup.mm"
include "cvv.mm"
include "wcel.mm"
include "id.mm"
include "supexd.mm"
include "ax-mp.mm"

theorem supex
  let cA: class A
  let cB: class B
  let cR: class R
  assume supex.1: |- R Or A


  assert |- sup ( B , A , R ) e. _V

  proof
    cA
    cR
    wor
    #
    cB
    cA
    cR
    csup
    cvv
    wcel
    supex.1
    @0
    cA
    cB
    cR
    @0
    id
    supexd
    ax-mp
end
