include "wor.mm"
include "cinf.mm"
include "cvv.mm"
include "wcel.mm"
include "id.mm"
include "infexd.mm"
include "ax-mp.mm"

theorem infex
  let cA: class A
  let cB: class B
  let cR: class R
  assume infex.1: |- R Or A


  assert |- inf ( B , A , R ) e. _V

  proof
    cA
    cR
    wor
    #
    cB
    cA
    cR
    cinf
    cvv
    wcel
    infex.1
    @0
    cA
    cB
    cR
    @0
    id
    infexd
    ax-mp
end
